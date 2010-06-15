/* Context-free art ----> js+canvas compiler/interpreter. */

var CFA = (function() {
   // --------- Preliminaries: Math. ------------
   var vect_x_mat = function(v,m) {
      return [v[0] * m[0] + v[1] * m[2] + m[4],
	      v[0] * m[1] + v[1] * m[3] + m[5]];
   };
   
   var mat_x_mat = function(a,b) {
      b_no_t = [b[0],b[1],b[2],b[3],0,0]; // b minus its translation
      va = [a[0],a[1]];
      vb = [a[2],a[3]];
      vc = [a[4],a[5]];
      
      va_t = vect_x_mat(va, b_no_t);
      vb_t = vect_x_mat(vb, b_no_t);
      vc_t = vect_x_mat(vc, b); // include translation.
      
      return [va_t[0],va_t[1],vb_t[0],vb_t[1],vc_t[0],vc_t[1]];
   };

   // -------- Preliminaries : Parsing framework. -----------------
   var chomp = function(str) {
      if (str.length == 0)
	 return str;
      var i = 0;
      while (i < str.length) {
	 if (/\s/m.test(str[i])) {
	    i++;
	 } else {
	    if (str[i] == '/' && (i + 1 < str.length) && str[i+1] == "/") {
	       while (i < str.length && str[i] != "\n") 
		  i++;
	    }
	    else if (str[i] == "/" && (i + 1 < str.length) && str[i+1] == "*") {
	       while (i < str.length && !(str[i] == '/' && str[i-1] == "*"))
		  i++;
	       i++; // one extra to go past the final slash
	    }
	    else return str.substr(i);
	 }
      }

   };

   // Simple combinator parsers. Not particularly efficient.
   var p = function(rx) { // parse a regex.
      return (function(instr) {
	 var str = chomp(instr);
	 var m = rx.exec(str);
	 if (null == m) 
	    return [];
	 if (m.index != 0) { // not at beginning.
	    return [];
	 }
	 return [[m[1], str.substr(m.index + m[0].length)]]; // return 1st paren group
      });
   };

   var alt = function() {
      var alts = arguments;
      return (function(str) {

	 var rs = [];
	 for (var i = 0; i < alts.length; i++) {
	    var res = alts[i](str);
	    rs.push(res);
	 }

	 return [].concat.apply([], rs);
      });
   };
   
   var seq_i = function(a,b) { // sequence two parsers
      return function(str) {
	 var res_a = a(str);
	 var res_fin = [];
	 for (var i = 0; i < res_a.length; i++) {
	    var ra = res_a[i];
	    var a_obj = ra[0];
	    var res_b = b(ra[1]);
	    for (var j = 0; j < res_b.length; j++) {
	       var rb = res_b[j];
	       var b_obj = rb[0];
	       res_fin.push( [[a_obj,b_obj], rb[1]] );
	    }
	 }

	 return res_fin;
      }
   };

   var app = function(parser, fn) { // apply a fn to the result of a parse
      return function(str) {
	 var res = parser(str);
	 for (var i = 0; i < res.length; i++)
	    res[i][0] = fn(res[i][0]);
	 return res;
      };
   }

   var succeed = function(v) {
      return function(str) {
	 return [[v,str]];
      };
   };

   var seq = function(parsers, fn) { 
      // Helper: parse 'parsers' in a row, then apply the target fn. 
      var s = succeed([]);
      for (var i = parsers.length - 1; i >= 0; i--) {
	 s = (function(ns) { return seq_i(parsers[i], ns); })(s);
      }

      var flatten_seq_res = function(vs) {
	 var r = [];
	 var v = vs;

	 while (v.length > 0) {
	    r.push(v[0]);
	    v = v[1];
	 }

	 return r;
      }
      var app_i = function(r) {
	 return fn.apply("_no_this", flatten_seq_res(r));
      }

      return app(s, app_i);
   };

   var many = function(parser) {
      return function(str) {
	 return alt(succeed([]),
		    seq([parser, many(parser)], 
			function(hd,rest) {
			   return [hd].concat(rest); }))(str);
      };
   };

   var some = function(p) { return seq([p,many(p)],
				      function(hd,rst) { return [hd].concat(rst);} ); };

   var end_of_input = function(instr) {
      var str = chomp(instr);
      if (typeof(str) == 'undefined' || str.length == 0) {
	 return [ [true, ""] ];
      }
      else return [];
   }

   var lit = function(x) { return p(new RegExp("(" + x + ")")); }

   // ------ Context Free Art -----------
   
   // AST constructors
   var startshape = function(nm) {
      return function(cfa) { cfa.startshape = nm; };
   };
   var rule = function(nm,prob,body) {
      return function(cfa) { 
	 if (!!!cfa.rules[nm])
	    cfa.rules[nm] = [];
	 cfa.rules[nm].push([prob,body]);
      };
   };
   var include = function(incpath) {
      return function(cfa) {
	 if (!cfa.inc_warned)
	    console.log("Warning: includes not supported.");
	 cfa.inc_warned = true;
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


   // Sequence function of (state, cc) in continuation-passing style.
   // --
   var seq_cps = function(fns) {
      if (fns.length == 0)
	 return function(st,cc) { return cc(); }
      if (fns.length == 1)
	 return fns[0];
      var hd = fns.shift();
      var tl = seq_cps(fns);
      return function(st,cc) {
	 return hd(st, function() { return tl(st,cc); });
      }
   }

   var compile_rule_body = function(bdy) { return seq_cps(bdy); }

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
      for (var i = 0; i < splits.length; i++) {
	 splits[i] = cur + ((1.0 / tot) * splits[i]);
	 cur = splits[i];
      }

      return function(state,cc) {
	 r = Math.random();
	 for (var i = 0; i < rs.length; i++) {
	    if (r < splits[i])
	       return rs[i](state,cc);
	 }
	 console.log("Badness in weighted random?");
	 return rs[0](state,cc);
      };
   }

   // Apply a rule w/ given adjustments!
   // ...Recursion happens here..
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
   }

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
	 }
      }

      var hd = action;
      var rest = ntimes_apply(count-1,action,adj);
      
      return function(state, cc) {
	 adj(state);
	 return hd(state, function() { return rest(state, cc); });
      }
   }

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
	 if (v < 0.0)
	    tgt = 0.0;
	 return function(state) {
	    var diff = (tgt - state.color[component]);
	    var fin = state[nm][component] + (adj * diff);
	    if (fin < 0) 
	       fin = 0
	    if (fin > 1)
	       fin = 1
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
	    state.color[component] += (adj * diff);
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
   var tx = function(mat) {
      return function(state) {
	 state.transform = mat_x_mat(mat, state.transform);
      };
   };
   var translate = function(x,y) { return tx([1,0,0,1,x,y]); };
   var scale = function(x,y) { return tx([x,0,0,y,0,0]); };
   var skew = function(ydeg,xdeg) {
      yrad = Math.PI * ydeg / 180.0;
      xrad = Math.PI * xdeg / 180.0;
      var new_x_x = Math.cos(xrad);
      var new_x_y = Math.sin(xrad);
      var new_y_x = -Math.sin(yrad);
      var new_y_y = Math.cos(yrad);
      return tx( [new_x_x,new_x_y,new_y_x,new_y_y,0,0]);
   };
   var rot = function(deg) {
      var rad = Math.PI * deg / 180.0;
      var xv = Math.cos(rad);
      var yv = Math.sin(rad);
      return tx([xv,yv,-yv,xv,0,0]);
   };
   var flip = function(deg) {
      var rad = Math.PI * deg / 180.0;
      var yv = Math.sin(rad);
      var xv = Math.cos(rad);
      var rotmat = [xv,yv,-yv,xv,0,0];
      var mat = mat_x_mat([-1,0,0,1,0,0],rotmat);
      return tx(mat);
   }


   var compile_adjustment = function(adjs) {
      // TODO: pull out all the transformations into just one.
      return function(state) {
	 for (var i = 0; i < adjs.length; i++) {
	    adjs[i](state);
	 }
      }
   }

   var reorder = function(adjs) {
      // Order by: translation, then rotation, then scaling, then skews, 
      //  and finally flips.
      return adjs;
   };

   // Path operations: 
   // ----------------
   var pathfun = function(nm) {
      return function() {
	 var args = arguments;
	 return function(ctx) {
	    ctx[nm].apply(ctx,args);
	 }
      }
   }
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

      if (l <= 1)
	 s = s / l;
      else 
	 s = s / (2 - l);



      var a = c[3];
      var result = "hsla(" + h + "," + (s * 100) + "%," + (l * 100) + "%," + a + ")"
      return result;
   }
   var builtin_circle = function(state, cc) {
      var c = state.cfa.canvas;
      c.fillStyle= trans_color(state.color);
      c.setTransform.apply(c,state.transform);
      c.beginPath();
      c.arc(0,0,0.5,0, Math.PI*2,true);
      c.closePath();
      c.fill();
      return cc;
   }
   
   var builtin_square = function(state,cc) {
      var c = state.cfa.canvas;
      c.fillStyle= trans_color(state.color);
      c.setTransform.apply(c,state.transform);
      c.fillRect(-0.5,-0.5,1,1);
      return cc;
   }


   var ident = p(/([a-zA-Z0-9]+)/);
   var fname = p(/"?([a-zA-Z0-9.]+)"?/);
   var number = app(p(/([-+]?[0-9]*\.?[0-9]+)/), parseFloat);
   var parse_cva = function(str) {

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
	  seq([lit('\\|'),alt(lit('hue'),lit('h')), number], 
	      function(_,_,h) { return hue_settgt(h); }),
	  seq([lit('\\|'),alt(lit('saturation'),lit('sat')), number], 
	      function(_,_,_v) { return saturation_settgt(v); }),
	  seq([lit('\\|'),alt(lit('brightness'),lit('b')), number], 
	      function(_,_,v) { return brightness_settgt(v); }),
	  seq([lit('\\|'),alt(lit('alpha'),lit('a')), number], 
	      function(_,_,v) { return alpha_settgt(v); }),

	  // Move drawing color closer to target color:
	  seq([alt(lit('hue'),lit('h')), number,lit('\\|')], 
	      function(_,h,_) { return hue_tgt(h); }),
	  seq([alt(lit('saturation'),lit('sat')), number, lit('\\|')], 
	      function(_,v,_) { return saturation_tgt(v); }),
	  seq([alt(lit('brightness'),lit('b')), number, lit('\\|')], 
	      function(_,v,_) { return brightness_tgt(v); }),
	  seq([alt(lit('alpha'),lit('a')), number,lit('\\|')], 
	      function(_,v,_) { return alpha_tgt(v); })

	  );
	  
      var adjustment = alt(seq([p(/(\[)/), many(adj), p(/(\])/)], function(_,adjs,_) {  return compile_adjustment(adjs); }),
			   seq([p(/(\{)/), many(adj), p(/(\})/)], function(_,adjs,_) { return compile_adjustment(reorder(adjs)); }));
			   

      // Read a rule!
      var ntimes = seq([number,lit('\\*'),adjustment,ident,adjustment],
		       function(count,_,adj1,nm,adj2) {
			  return ntimes_apply(count, apply_rule(nm,adj2),adj1);
		       });
      
      var statement = alt(seq([ident, adjustment],
			  function(nm,adj) { return apply_rule(nm,adj); }),
			  ntimes);
      var rbody = seq([p(/(\{)/),some(statement), p(/(\})/)],
		      function(_,b,_) { return b; });


      var p_rule = 
      //alt(
	  seq([lit("rule"), ident, alt(number, succeed(1.0)) ,rbody],
	      function(_,nm,wt,bdy) { return rule(nm,wt,bdy); });
	  //seq([lit("rule"), ident, number, rbody],
	  //    function(_,nm,weight,body) { return rule(nm,weight,body); })
	 //);

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
      var result = 
      seq([many(directive),end_of_input], function(r,_) { return r;})(str);
      
      var ncfa = {
	 rules : {},
	 start_rule : "",
	 compiled_rules : {
	     'CIRCLE' : builtin_circle,
	    'SQUARE' : builtin_square,
	    'TRIANGLE' : builtin_square
	 },
	 background : [0,0,1,1],
	 paths : {},
      };
      
      var res_p = result[0][0];
      for (var i = 0; i < res_p.length; i++) {
	 res_p[i](ncfa);
      }
      return ncfa;
   };

   var default_opts = {
      recurse : function(f,state,cc) {
	 var t = state.transform
	 var xlen_sq = t[0] * t[0] + t[1]*t[1];
	 var ylen_sq = t[2] * t[2] + t[3]*t[3];
	 if (xlen_sq < 0.05 | ylen_sq < 0.05) { 
	    // when we're small, call it done.
	    return cc;
	 }
	 if (state.depth > 10000) {
	    return cc;
	 } else
	 return function() { return f(state,cc) };
      },
      cont : function(cc) {
	 return cc; // Note the missing call parens! trampolined style.
      }
   };
   
   var sampling_opts = {
      recurse : function(f,state,cc) {
	 var xlen_sq = t[0] * t[0] + t[1]*t[1];
	 var ylen_sq = t[2] * t[2] + t[3]*t[3];
	 if (xlen_sq < 0.5 | ylen_sq < 0.5)
	    return cc;
	 if (state.depth > 1000)
	    return cc;
	 return function() { return f(state,cc); }
      },
      cont : function(cc) { return cc; }
   }

   var call_trampoline = function(f) {
      var cur = f;
      var count = 0;
      while (typeof(cur) == 'function') {
	 cur = cur();
	 count = count + 1;
	 if (count > 1000) { // 1ms pause every 1000 bounces.
	    window.setTimeout(function() {
	       call_trampoline(cur);
	    }, 1);
	    return;
	 }
      }
      return cur;
   }

   return {
      parse : function(taid) {
	 var ta = document.getElementById(taid);
	 var v = (ta.value);
	 var r = (parse_cva(v));
	 return r;
      },
      exec : function(cfa, w,h,canvas_id, exec_opts) {
	 if (!exec_opts)
	    exec_opts = default_opts;

	 cfa.recurse = exec_opts.recurse;
	 cfa.cont = exec_opts.cont;

	 var canvas = document.getElementById(canvas_id);
	 
	 cfa.canvas = canvas.getContext('2d');
	 cfa.canvas.setTransform(1,0,0,1,0,0);
	 cfa.canvas.fillStyle = trans_color(cfa.background);
	 cfa.canvas.fillRect(0,0,w,h);

	 // TODO: Determine bounding box by sampling the shape:
	 var initial_adj = compile_adjustment([scale(0.2,0.2)]);
	 
	 var initial_state = {
	    color : [0,0,0,1],
	    target_color : [0,0,0,1],
	    transform : [w/2.0,0,0,-1.0 * h/2.0,w/2.0,h/2.0],
	    cfa : cfa,
	    depth : 0
	 };
	 
	 var fin_cc = function() { console.log("done"); }
	 var go = apply_rule(cfa.startshape, initial_adj);
	 call_trampoline(function() { return go(initial_state, fin_cc); });
      },
      default_opts : default_opts
   }

})();