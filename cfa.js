/* Context-free art ----> js+canvas interpreter. */
/* License: GPL! */
/* Fixme: flesh that out. */
var CFA = (function() {
   var console_a = { log : function() { } };
   if (typeof(console) == 'undefined') {
      console = console_a;
   }
   // --------- Preliminaries: Math. ------------
   var vect_x_mat = function(v,m) {
      return [v[0] * m[0] + v[1] * m[2] + m[4],
	      v[0] * m[1] + v[1] * m[3] + m[5]];
   };
   
   var mat_x_mat = function(a,b) {
      var b_no_t = [b[0],b[1],b[2],b[3],0,0]; // b minus its translation
      var va = [a[0],a[1]];
      var vb = [a[2],a[3]];
      var vc = [a[4],a[5]];
      
      var va_t = vect_x_mat(va, b_no_t);
      var vb_t = vect_x_mat(vb, b_no_t);
      var vc_t = vect_x_mat(vc, b); // include translation.
      
      return [va_t[0],va_t[1],vb_t[0],vb_t[1],vc_t[0],vc_t[1]];
   };

   // -------- Preliminaries : Parsing framework. -----------------
   var Parsing = function() {
      var State = function (str,idx,line,col) {
	 return {
	    idx : idx,
	    eof : (idx+1) >= str.length,
	    cur : str[idx],
	    str : str,
	    peek2 : str[idx] + (function() { 
	       return ((idx+1) < str.length) ? str[idx + 1] : ""; 
	    })(),
	    advance : function() {
	       if (this.cur == "\n") {
		  return new State(str,idx+1,line+1,0);
	       } else {
		  return new State(str,idx+1,line,col+1);
	       }
	    },
	    txt : function () { return str.substring(idx); }
	 };
      };

      var win = function(result,st) {
	 return [ [true, result, st] ];
      };

      var lose = function(msg, st) {
	 return  [ [false, msg, st] ];
      };
      var wins = function(res) {
	 var r = [];
	 for (var i = 0; i < res.length; i++) {
	    if (res[i][0] == true) { 
	       r.push(res[i]); 
	    }
	 }
	 return r;
      };

      var r_advance = function(st) {
	 var s = st;
	 var done = true;
	 do {
	    done = true;
	    if (/\s/.test(s.cur)) { done = false; }
	    if (s.peek2 == "//") {  // cpp comment
	       while (!s.eof && s.cur != "\n") {
		  s = s.advance();
	       }
	       done = false;
	    }
	    if (s.peek2 == "/*") {  // c comment
	       while (!s.eof && s.peek2 != "*/") {
		  s = s.advance();
	       }
	       s = s.advance(); // extra advance for final slash
	       done = false;
	    }
	    if (!done) { s = s.advance(); }
	 } while (!done);
	 return s;
      };
      
      // Parser that consumes nothing and succeeds
      var succeed = function(v) {
	 return function(st) { 
	    return win(v,st);
	 };
      };

      // Parser that fails
      var fail = function() {
	 return function(st) { return lose("failed",st); };
      };

      // Make a nonterminal whose contents are initially empty:
      var nt = function () {
	 var res = function(st) {
	    return res.inner(st);
	 };
	 res.inner = fail();
	 return res;
      };

      // Parser for a regex.
      var p = function(rx, nm) {
	 return function(st) {
	    var s = r_advance(st);
	    var t = s.txt();
	    var m = rx.exec(t);
	    if (null === m || m.index !== 0) {
	       return lose("Expecting a " + nm, st);
	    }
	    var result = m[0];
	    for (var i = 0 ; i < result.length; i++) {
	       s = s.advance();
	    }
	    return win(result,s);
	 };
      };

      // Parser for a literal
      var lit = function(l) {
	 return function(st) {
	    var s = r_advance(st);
	    var idx = 0;
	    while (idx < l.length) {
	       if (l[idx] != s.cur) {
		  return lose("Expecting '" + l + "'",s); 
	       }
	       s = s.advance();
	       idx++;
	    }
	    return win(l,s);
	 };
      };

      // Sequence two parsers:
      var seq_i = function(a,b) {
	 return function(st) {

	    var a_raw_res = a(st);
	    var ares = wins(a_raw_res);
	    if (ares.length == 0) { return a_raw_res; }

	    var fin = [];
	    for (var i = 0; i < ares.length; i++) {
	       var aobj = ares[i][1];
	       var ast = ares[i][2];

	       var b_raw_res = b(ast);
	       var bres = wins(b_raw_res);
		       
	       for (var j = 0; j < bres.length; j++) {
		  var br = bres[j];
		  if (br[0]) {

		     fin.push([true, [aobj, br[1]], br[2]]);
		  } else {
		     fin.push(br);
		  }
	       }
	
	    }
	    return fin;

	 };
      };

      // Alternatives:
      var alt = function() {
	 var alts = arguments;
	 return function(st) {
	    var res = [];
	    for (var i = 0; i < alts.length; i++) {
	       res = res.concat(alts[i](st));
	    }
	    return res;
	 };
      };

      // Apply function to parser results:
      var app = function(parser, fn) {
	 return function(st) {
	    var res = parser(st);
	    for (var i = 0; i < res.length; i++) {
	       if (res[i][0]) {
		  res[i][1] = fn(res[i][1]);
	       }
	    }
	    return res;
	 };
      };

      // internal helper: list cons.
      var lstcons = function(a,b) {
	 var r = [a].concat(b);
	 return r;
      };

      // Helper: parse 'parsers' in a row, then apply the target fn. 
      var seq = function(parsers, fn) {
	 var imp = function(ps) {
	    if (ps.length == 0) { return succeed([]); };
	    var hd = ps[0];
	    ps.shift();
	    var rst = imp(ps);
	    return seq_i(hd,rst);
	 };

	 var fltn = function(ks) {
	    var r = [];
	    var cur = ks;
	    while (cur.length > 0) {
	       r.push(cur[0]);
	       cur = cur[1];
	    }
	    return r;
	 };

	 return app(imp(parsers), function(x) {
	    return fn.apply([],fltn(x)); 
	 });
      };
      
      var many = function(parser) {
	 var many_i = nt();
	 many_i.inner = alt(succeed([]),
			    seq([parser,many_i], lstcons));
	 return many_i;
      };

      var some = function(parser) {
	 return seq([parser,many(parser)], lstcons);
      };

      var end_of_input = function(st) {
	 var s = r_advance(st);

	 if (s.eof)
	    { return win(true,s); }
	 else
	    { return lose("Extra input after end:" + s.txt(),s); }
      };

      return {
	 init : function(str) { return new State(str,0,0,0); },
	 succeed : succeed,
	 fail : fail,
	 nt : nt,
	 p : p,
	 lit : lit,
	 seq : seq,
	 alt : alt,
	 some : some,
	 many : many,
	 eof : end_of_input,
	 wins : wins,
	 app : app
      };
   };

   // ------ Context Free Art -----------
   
   // AST constructors
   var startshape = function(nm) {
      return function(cfa) { cfa.startshape = nm; };
   };
   var rule = function(nm,prob,body) {
      return function(cfa) { 
	 if (!!!cfa.rules[nm]) { cfa.rules[nm] = []; }
	 cfa.rules[nm].push([prob,body]);
      };
   };
   var include = function(incpath) {
      return function(cfa) {
	 console.log("Warning: includes not supported.");
      };
   };
   var tile = function(ignored) {
      return function(cfa) {
	 console.log("Warning: tiling not supported.");
      };
   };
   var bkgd = function(color_trans) {
      return function(cfa) {
	 console.log("applying bkgd", color_trans);
	 var dummy_state = { color : [0,0,1,1] };
	 color_trans(dummy_state);
	 cfa.background = dummy_state.color;
      };
   };
   var path = function(nm, cmds) {
      return function(cfa) {
	 cfa.paths[nm] = cmds;
      };
   };


   // Sequence functions of (state, cc) in continuation-passing style.
   // --
   var seq_cps = function(fns) {
      if (fns.length === 0) { return function(st,cc) { return cc(); }; }
      if (fns.length == 1) { return fns[0]; }

      var hd = fns.shift();
      var tl = seq_cps(fns);
      return function(st,cc) {
	 return hd(st, function() { return tl(st,cc); });
      };
   };

   var compile_rule_body = seq_cps; 

   var compile_rule = function(rule_bodies) {
      var splits = [];
      var rs = [];
      var tot = 0.0;
      for (var i = 0; i < rule_bodies.length; i++) {
	 rs.push(compile_rule_body(rule_bodies[i][1]));
	 tot += rule_bodies[i][0];
	 splits.push(rule_bodies[i][0]);
      }

      var cur = 0.0;
      for (var ii = 0; ii < splits.length; ii++) {
	 splits[ii] = cur + ((1.0 / tot) * splits[ii]);
	 cur = splits[ii];
      }

      return function(state,cc) {
	 var r = Math.random();
	 for (var i = 0; i < rs.length; i++) {
	    if (r < splits[i]) { return rs[i](state,cc); }
	 }
	 console.log("Badness in weighted random?");
	 return rs[0](state,cc);
      };
   };

   var with_saved_state = function(callback, state, cc) {
      // Save the state:
      var depth = state.depth;
      var cfa = state.cfa;
      var color = [].concat(state.color);
      var transform = [].concat(state.transform);
      var target_color = [].concat(state.target_color);

      // Construct continuation that restores state.
      var cont = function() {
	 state.depth = depth;
	 state.cfa = cfa;
	 state.color = [].concat(color);
	 state.transform = [].concat(transform);
	 state.target_color = [].concat(target_color);
	 return state.cfa.cont(cc);
      };

      return callback(state,cont);
   };

   // Apply a rule w/ given adjustments!
   // ...Recursion happens here..
   var apply_rule = function(nm, trans) {
      return function(state, cc) {
	 
	 var cfa = state.cfa; 

	 // Lazy compile if needed:
	 if (!!!cfa.compiled_rules[nm]) {

	    console.log("compiling: " + nm);
	    cfa.compiled_rules[nm] = compile_rule(state.cfa.rules[nm]);
	 }

	 return with_saved_state(function(state,cont) {
	    trans(state); // Apply the transform.
	    state.depth += 1;
	    
	    // Call the rule. (With recursion-limiting wrapper.)
	    return cfa.recurse(cfa.compiled_rules[nm], state, cont);
	 }, state, cc);

      };
   };

   var ntimes_apply = function(count, action, adj) {
      if (0 >= count) { 
	 return function(state,cc) {
	    return state.cfa.cont(cc);
	 };
      }

      var hd = action;
      var rest = ntimes_apply(count-1,action,adj);
      
      return function(state, cc) {
	 adj(state);
	 return hd(state, function() { return rest(state, cc); });
      };
   };

   // Color adjustments 
   // -----------------
   var hue_i = function(nm) {
      return function(v) {
	 return function(state) {
	    state[nm][0] = ((state[nm][0] + v) % 360);
	 };
      };
   };

   var hue = hue_i("color");
   var mult_color_adjust = function(nm,component) {
      return function(v) {
	 var adj = Math.abs(v);
	 var tgt = 1.0;
	 if (v < 0.0) { tgt = 0.0; }
	 return function(state) {
	    var diff = (tgt - state.color[component]);
	    var fin = state[nm][component] + (adj * diff);
	    if (fin < 0) { fin = 0; }
	    if (fin > 1) { fin = 1; }
	    state[nm][component] = fin;
	 };
      };
   };
   var tgt_color_adjust = function(component) {
      return function(v) {
	 var adj = v;

	 return function(state) {
	    var tgt = state.target_color[component];
	    var diff = (tgt - state.color[component]);
	    var fin = state.color[component] + (adj * diff);
	    if (fin < 0) { fin = 0; }
	    if (fin > 1) { fin = 1; }
	    state.color[component] = fin;
	 };
      };
   };
   var saturation = mult_color_adjust("color",1);
   var saturation_tgt = tgt_color_adjust(1);
   var brightness = mult_color_adjust("color",2);
   var brightness_tgt = tgt_color_adjust(2);
   var alpha = mult_color_adjust("color",3);
   var alpha_tgt = tgt_color_adjust(3);
   var hue_tgt = tgt_color_adjust(0);
   var hue_settgt = hue_i("target_color");
   var saturation_settgt = mult_color_adjust("target_color",1);
   var brightness_settgt = mult_color_adjust("target_color",2);
   var alpha_settgt = mult_color_adjust("target_color",3);

   // Shape adjustments
   // -----------------
   var tx = function(p,mat) {
      var res = function(state) {
	 state.transform = mat_x_mat(mat, state.transform);
      };
      res.sort_order = p;
      return res;
   };
   var translate = function(x,y) { return tx(4,[1,0,0,1,x,y]); };
   var scale = function(x,y) { return tx(2,[x,0,0,y,0,0]); };
   var skew = function(ydeg,xdeg) {
      var yrad = Math.PI * ydeg / 180.0;
      var xrad = Math.PI * xdeg / 180.0;
      var new_x_x = Math.cos(xrad);
      var new_x_y = Math.sin(xrad);
      var new_y_x = -Math.sin(yrad);
      var new_y_y = Math.cos(yrad);
      return tx(1,[new_x_x,new_x_y,new_y_x,new_y_y,0,0]);
   };
   var rot = function(deg) {
      var rad = Math.PI * deg / 180.0;
      var xv = Math.cos(rad);
      var yv = Math.sin(rad);
      return tx(3,[xv,yv,-yv,xv,0,0]);
   };

   var flip = function(deg) {
      var rad = Math.PI * (deg) / 180.0;
      var xv = Math.cos(rad);
      var yv = Math.sin(rad);
      var yvsq = yv * yv;
      var vxvy = xv * xv - yv * yv;
      var vyvx = yv * yv - xv * xv;
      var mat = [vxvy, 2*xv*yv, 2*xv*yv,vyvx,0,0];
      return tx(0,mat);
   };


   var compile_adjustment = function(adjs) {
      // TODO: pull out all the transformations into just one
      //   and premultiply.
      return function(state) {
	 for (var i = 0; i < adjs.length; i++) {
	    adjs[i](state);
	 }
      };
   };

   var reorder = function(adjs) {
      var ordering = function(x) { 
	 if (!!x.sort_order) { return x.sort_order; }
	 else { return -1; }
      };
      
      // Order by: translation, then rotation, then scaling, then skews, 
      //  and finally flips.
      // (values are passed in the tx constructor.)
      adjs.sort(function(a,b) { return ordering(b) - ordering(a); });

      return adjs;
   };

   // Path operations: 
   // ----------------
   var pathfun = function(nm) {
      return function() {
	 var args = arguments;
	 return function(ctx) {
	    ctx[nm].apply(ctx,args);
	 };
      };
   };
   var moveto = pathfun("moveTo");
   var lineto = pathfun("lineTo");
   var curveto = pathfun("");
   

   var idgen = 0;

   var trans_color = function(c) {
      // HSB is the same as HSV? but canvas knows HSL.
      // http://wiki.secondlife.com/wiki/Color_conversion_scripts#HSL_to_HSV
      var insat = c[1];
      var inval = c[2];

      var h = c[0]; // hue stays the same.

      var l = (2 - insat) * (inval * 0.5);
      var s = insat * inval;

      if (l <= 1) { s = s / l; }
      else { s = s / (2 - l); }
      
      if (isNaN(s)) { s = 0; }

      var a = c[3];
      var result = "hsla(" + h + "," + (s * 100) + "%," + (l * 100) + "%," + a + ")";

      return result;
   };

   var builtin_circle = function(state, cc) {
      var c = state.cfa.canvas;
      c.fillStyle= trans_color(state.color);
      c.setTransform.apply(c,state.transform);
      c.beginPath();
      c.arc(0,0,0.5,0, Math.PI*2,true);
      c.closePath();
      c.fill();
      return cc;
   };
   
   var builtin_square = function(state,cc) {
      var c = state.cfa.canvas;
      c.fillStyle= trans_color(state.color);
      c.setTransform.apply(c,state.transform);
      c.beginPath();
      c.moveTo(-0.5,-0.5);
      c.lineTo(0.5,-0.5);
      c.lineTo(0.5,0.5);
      c.lineTo(-0.5,0.5);
      c.closePath();
      c.fill();
      return cc;
   };

   var h = 0.5 / (Math.cos(Math.PI/6.0));
   var hp = h;
   var hn = -h / 2.0;
   var builtin_triangle = function(state,cc) {
      var c = state.cfa.canvas;
      c.fillStyle = trans_color(state.color);
      c.beginPath();
      c.moveTo(0,hp);
      c.lineTo(-0.5,hn);
      c.lineTo(0.5,hn);
      c.lineTo(0.0,hp);
      c.closePath();
      c.fill();
      return cc;
   };

   var builtins = function() { return {
	 'CIRCLE' : builtin_circle,
	 'SQUARE' : builtin_square,
	 'TRIANGLE' : builtin_triangle };
   };
   var parse_cva = function(str) {
      var Pr = Parsing();

      // *sigh* I should use the 'with' statement. 
      var succeed = Pr.succeed; var fail = Pr.fail; var nt = Pr.nt; var p = Pr.p; var lit = Pr.lit;
      var seq = Pr.seq; var alt = Pr.alt; var some = Pr.some; var many = Pr.many; var eof = Pr.eof;
      var app = Pr.app;

      var ident = p(/([a-zA-Z0-9]+)/, "identifier");
      var fname = p(/"?([a-zA-Z0-9.]+)"?/, "filename");
      var number = app(p(/([\-+]?[0-9]*\.?[0-9]+)/,"number"), parseFloat);

      // Adjustments:
      var adj = 
      alt(
	 // Shape adjustments:
	  seq([lit('x'),number], function(_,x) { return translate(x,0.0); }),
	  seq([lit('y'), number], function(_,y) { return translate(0.0,y); }),
	  seq([lit('z'), number], function(_,y) { return translate(0.0,0.0); }),
	  seq([alt(lit('size'),lit('s')),number], function(_,s) { return scale(s,s); }),
	  seq([alt(lit('size'),lit('s')),number,number], 
	      function(_,sx,sy) { return scale(sx,sy); }),
	  seq([alt(lit('size'),lit('s')),number,number,number], 
	      function(_,sx,sy,sz) { return scale(sx,sy); }),
	  seq([alt(lit('rotate'),lit('r')),number],
	     function(_,f) { return rot(f); }),
	  seq([alt(lit('flip'),lit('f')),number],
	     function(_,f) { return flip(f); }),
	  seq([lit('skew'),number, number], 
	     function(_,a,b) { return skew(a,b); }),

	  // Color adjustments.
	  seq([alt(lit('hue'),lit('h')), number], 
	      function(_,h) { return hue(h); }),
	  seq([alt(lit('saturation'),lit('sat')), number], 
	      function(_,v) { return saturation(v); }),
	  seq([alt(lit('brightness'),lit('b')), number], 
	      function(_,v) { return brightness(v); }),
	  seq([alt(lit('alpha'),lit('a')), number], 
	      function(_,v) { return alpha(v); }),

	  // Adjust target color:
	  seq([lit('|'),alt(lit('hue'),lit('h')), number], 
	      function(_,_,h) { return hue_settgt(h); }),
	  seq([lit('|'),alt(lit('saturation'),lit('sat')), number], 
	      function(_,_,v) { return saturation_settgt(v); }),
	  seq([lit('|'),alt(lit('brightness'),lit('b')), number], 
	      function(_,_,v) { return brightness_settgt(v); }),
	  seq([lit('|'),alt(lit('alpha'),lit('a')), number], 
	      function(_,_,v) { return alpha_settgt(v); }),

	  // Move drawing color closer to target color:
	  seq([alt(lit('hue'),lit('h')), number,lit('|')], 
	      function(_,h,_) { return hue_tgt(h); }),
	  seq([alt(lit('saturation'),lit('sat')), number, lit('|')], 
	      function(_,v,_) { return saturation_tgt(v); }),
	  seq([alt(lit('brightness'),lit('b')), number, lit('|')], 
	      function(_,v,_) { return brightness_tgt(v); }),
	  seq([alt(lit('alpha'),lit('a')), number,lit('|')], 
	      function(_,v,_) { return alpha_tgt(v); })

	  );
	  
      var adjustment = alt(seq([lit("["), many(adj), lit("]")], function(_,adjs,_) {  return compile_adjustment(adjs); }),
			   seq([lit("{"), many(adj), lit("}")], function(_,adjs,_) { return compile_adjustment(reorder(adjs)); }));
			   

      // Read a rule!
      var ntimes = seq([number,lit('*'),adjustment,ident,adjustment],
		       function(count,_,adj1,nm,adj2) {
			  return ntimes_apply(count, apply_rule(nm,adj2),adj1);
		       });
      
      var statement = alt(seq([ident, adjustment],
			  function(nm,adj) { return apply_rule(nm,adj); }),
			  ntimes);
      var rbody = seq([lit("{"),some(statement), lit("}")],
		      function(_,b,_) { return b; });


      var p_rule = seq([lit("rule"), ident, alt(number, succeed(1.0)) ,rbody],
		       function(_,nm,wt,bdy) { return rule(nm,wt,bdy); });

      // directives
      var directive = alt(seq([lit("startshape"), ident], 
			      function(_,nm) { return startshape(nm); }),
			  seq([lit("include"), fname],
			      function(_,nm) { return include(nm); }),
			  seq([lit("tile"), adjustment], 
			      function(_,adj) { return tile(adj); }),
			  p_rule,
			  seq([lit("background"),adjustment],
			      function(_,adj) { return bkgd(adj); })
			  );

      
      // Actually run the parse:
      //var result = seq([ident,many(alt(number,ident)),eof],function(a,b,_) { 
	// console.log("Success!",a,b);
	// return a; 
      //})(Pr.init(str));
      var result = seq([many(directive),eof], 
		       function(r,_) { return r;})(Pr.init(str));
      
      var w = Pr.wins(result);
      if (w.length == 0) {
	 var last_failure = result[result.length-1][1];
	 throw("Parsing error: " + last_failure);
      }

      var res_p = result[0][1];

      var ncfa = {
	 rules : {},
	 start_rule : "",
	 compiled_rules : builtins(),
	 background : [0,0,1,1],
	 paths : {}
      };
      
      for (var i = 0; i < res_p.length; i++) {
	 res_p[i](ncfa);
      }

      return ncfa;
   };

   var default_opts = {
      recurse : function(f,state,cc) {
	 var t = state.transform;
	 var xlen_sq = t[0] * t[0] + t[1]*t[1];
	 var ylen_sq = t[2] * t[2] + t[3]*t[3];
	 if (xlen_sq < 0.5 && ylen_sq < 0.5) { 
	    // when small, call it done.
	    return cc;
	 }
	 if (state.depth > 100000) { return cc; }
	 else { return function() { return f(state,cc); }; }
      },
      cont : function(cc) {
	 return cc; // Note the missing call parens! trampolined style.
      }
   };
   
   var builtin_nop = function(state,cc) { return cc; };

   var sampling_recursion = function(sampler) {
      return function(f,state,cc) {
	 var unitx = vect_x_mat([1,0],state.transform);
	 var unity = vect_x_mat([0,1],state.transform);

	 var s = function(usemin,vectidx,boxidx) {
	    var f = usemin ? Math.min : Math.max;
	    var nmin = f(sampler.bbox[boxidx],
			 unitx[vectidx],
			 unity[vectidx]);
	    if ((nmin < sampler.bbox[boxidx]) == usemin) {
	       sampler.delta[boxidx] = Math.abs(nmin - sampler.bbox[boxidx]);
	       sampler.bbox[boxidx] = nmin;
	    }
	 };
	 
	 s(true,0,0);
	 s(true,1,1);
	 s(false,0,2);
	 s(false,0,3);

	 var xlen_sq = Math.max(unitx[0],unity[0]);
	 xlen_sq *= xlen_sq;
	 var ylen_sq = Math.max(unitx[1],unity[1]);
	 ylen_sq *= ylen_sq;
	 if (xlen_sq < 0.5 | ylen_sq < 0.5) { return cc; }
	 if (state.depth > 100) { return cc; } // only 100 deep.

	 return function() { return f(state,cc); };
      };
   };

   var call_trampoline = function(f) {
      var halted = false;
      var call_imp = function(ff) {
	 var cur = ff;
	 var count = 0;
	 while (typeof(cur) == 'function') {
	    cur = cur();
	    if (halted) {
	       return;
	    }
	    count = count + 1;
	    if (count > 1000) { // 1ms pause every 1000 bounces.
	       window.setTimeout(function() {
		  call_imp(cur);
	       }, 10);
	       return;
	    }
	 }
	 return cur;
      };
      window.setTimeout(function() {
	 call_imp(f);
      }, 10);
      return function() { 
	 console.log("stopped.");
	 halted = true;
      };
   };

   var get_scale = function(cfa) {
      // "Quickly" sample a CFA to get an idea of extents.
      
      var stats = { bbox : [0,0,0,0], delta: [0,0,0,0] };
      // Save the old recursion function.
      var old_cont = cfa.cont;
      var old_recurs = cfa.recurse;
      var old_builtins = cfa.compiled_rules;
      cfa.compiled_rules = {
	 'TRIANGLE' : builtin_nop,
	 'SQUARE' : builtin_nop,
	 'CIRCLE': builtin_nop
      };

      cfa.cont = default_opts.cont;
      cfa.recurse = sampling_recursion(stats);
      
      var raw_trampoline = function(f) {
	 while (typeof(f) == 'function') {
	    f = f();
	 }
	 return f;
      };

      var bbox = [0,0,0,0];
      // Run a CFA for a bit to get a rough idea of its bbox.
      var initial_state = {
	 color : [0,0,0,1],
	 target_color : [0,0,0,1],
	 transform : [1,0,0,1,0,0],
	 cfa : cfa,
	 depth : 0
      };
      var initial_trans = compile_adjustment([]);
      var fin_cc = function() { stats.done = true; };
      var go = apply_rule(cfa.startshape,initial_trans);
      raw_trampoline(function() { return go(initial_state,fin_cc); } );

      if (!stats.done) {
	 alert("hrm");
      }
      
      // restore
      cfa.cont = old_cont;
      cfa.recurse = old_recurs;
      cfa.compiled_rules = old_builtins;
      
      // grow by last delta?
      /* stats.bbox[0] += -1 * stats.delta[0];
      stats.bbox[1] += -1 * stats.delta[1];
      stats.bbox[2] += stats.delta[2];
      stats.bbox[3] += stats.delta[3]; */
      return stats.bbox;
   };

   return {
      parse : function(taid) {
	 var ta = document.getElementById(taid);
	 var v = (ta.value);
	 var r = (parse_cva(v));
	 return r;
      },
      get_bbox : function(cfa) { return get_scale(cfa); },
      exec : function(cfa, bbox,canvas_id, exec_opts) {
	 if (!exec_opts) { exec_opts = default_opts; }


	 var canvas = document.getElementById(canvas_id);
	 var w = canvas.width;
	 var h = canvas.height; 
	 

	 cfa.canvas = canvas.getContext('2d');
	 cfa.canvas.setTransform(1,0,0,1,0,0);
	 cfa.canvas.fillStyle = trans_color(cfa.background);
	 cfa.canvas.clearRect(0,0,w,h);
	 cfa.canvas.fillRect(0,0,w,h);

	 var bw = bbox[2] - bbox[0];
	 var bh = bbox[3] - bbox[1];
	 var bx = bbox[0];
	 var by = bbox[1];
	 var scl = 1.0 / Math.max(bw,bh);
	 console.log("bbox",bbox, scl);
	 var initial_adj = compile_adjustment([scale(scl,scl),translate(-bx,-by)]);
	 
	 cfa.recurse = exec_opts.recurse;
	 cfa.cont = exec_opts.cont;

	 var initial_state = {
	    color : [0,0,0,1],
	    target_color : [0,0,0,1],
	    transform : [w,0,0,-1.0 * h,0.0,h],
	    cfa : cfa,
	    depth : 0
	 };
	 
	 var fin_cc = function() { console.log("done"); };
	 var go = apply_rule(cfa.startshape, initial_adj);
	 return call_trampoline(function() { return go(initial_state, fin_cc); });
      },
      default_opts : default_opts,
      parse_and_run : function(taid,w,h,canvas) {
	 var cfa = this.parse(taid);
	 var bbox = this.get_bbox(cfa);
	 var ncfa = this.parse(taid); // FIXME: reusing it should work but doesn't.
	 return this.exec(ncfa, w,h,bbox,canvas);
      }
   };

})();