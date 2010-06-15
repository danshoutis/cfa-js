/* Context-free art ----> js+canvas compiler/interpreter. */

var CFA = (function() {
   // --------- Preliminaries: Math. ------------
   var vect_x_mat = function(v,m) {
      return [v[0] * m[0] + v[0] * m[1] + m[4],
	      v[1] * m[2] + v[1] * m[3] + m[5]];
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

   var prty = function(a,f) {
      pstr = [];
      for (var i = 0; i < a.length; i++) {
	 if (!!a[i].pretty) 
	    pstr.push(a[i]);
	 else
	    pstr.push(a[i].pretty);
      }
      f.pretty = "" + pstr + "";
      return f;
   }

   // Simple combinator parsers. Not particularly efficient.
   var p = function(rx) { // parse a regex.
      return prty(arguments,function(instr) {
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
      return prty(arguments,function(str) {

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
	 var hmm = parser("");
	 if (hmm.length != 0) {
	    alert("aha!");
	    return;
	 }
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
	 if (!!cfa.rules[nm])
	    cfa.rules[nm] = [];
	 cfa.rules[nm].push([prob,body]);
      };
   };
   var include = function(incpath) {
      return function(cfa) {
	 if (!cfa.inc_warned)
	    alert("Warning: includes not supported.");
	 cfa.inc_warned = true;
      };
   };
   var tile = function(ignored) {
      return function(cfa) {
	 alert("Warning: tiling not supported.");
      };
   };
   var bkgd = function(color_trans) {
      return function(cfa) {
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
   var apply_rule = function(nm, trans) {
      return function(cfa) {
	 return function(state, cc) {
	    var nstate = {};
	    nstate.color = [].concat(state.color);
	    nstate.transform = [].concat(state.transform);
	    nstate.target_color = [].concat(state.target_color);
	    var cont = function() {
	       state.color = nstate.color;
	       state.transform = nstate.transform;
	       state.target_color = nstate.target_color;
	       return cc();
	    };
	    return cfa.compiled_rules[nm](cont);
	 };
      };
   };

   // Color adjustments 
   // -----------------
   var hue_i = function(nm) {
      return function(v) {
	 return function(state) {
	    state[nm][0] += (v % 360);
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
	    state[nm][component] += (adj * diff);
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
   var hue_tgt = tgt_color_adjust[0];
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
      return tx( [math.cos(xrad),math.sin(xrad),math.sin(yrad),math.cos(yrad),0,0] );
   };
   var rot = function(deg) {
      var rad = Math.PI * deg / 180.0;
      var yv = Math.sin(rad);
      var xv = Math.cos(rad);
      return tx([xv,yv,-yv,xv,0,0]);
   };

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

   var seq_csp = function(fns) {
      var fin = function(st, cc) { return cc(); };
      var cur = fin;
      for (var i = fns.length - 1; i >= 0; i--) {
	 var ff = fns[i];
	 var ncur = (function(rcur) { 
	    return function(st,cc) {
	       ff(st, function() { rcur(st,cc); });
	    };
	 })(cur);
	 cur = ncur;
      }
      return cur;
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
	  seq([lit('size'),number], function(_,s) { return scale(s,s); }),
	  seq([lit('size'),number,number], 
	      function(_,sx,sy) { return scale(sx,sy); }),
	  seq([lit('size'),number,number,number], 
	      function(_,sx,sy,sz) { return scale(sx,sy); }),
	  seq([lit('s'),number], function(_,s) { return scale(s,s); }),
	  seq([lit('s'),number,number], 
	      function(_,sx,sy) { return scale(sx,sy); }),
	  seq([lit('s'),number,number,number], 
	      function(_,sx,sy,sz) { return scale(sx,sy); }),
	 seq([lit('rotate'),number],
	     function(_,f) { return rotate(f); }),
	 seq([lit('r'),number],
	     function(_,f) { return rotate(f); }),
	 seq([lit('flip'),number],
	     function(_,f) { return flip(f); }),
	 seq([lit('f'),number],
	     function(_,f) { return flip(f); }),
	 seq([lit('skew'),number, number], 
	     function(a,b) { return skew(a,b); })
	  // TODO: color adjustments.
	  );
	  
      var adjustment = alt(seq([p(/(\[)/), many(adj), p(/(\])/)], function(_,adjs,_) {  return adjs; }),
			   seq([p(/(\{)/), many(adj), p(/(\})/)], function(_,adjs,_) { return reorder(adjs); }));
			   

      // Read a rule!
      var statement = seq([ident, adjustment],
			  function(nm,adj) { return apply_rule(nm,adj); })
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
			  p_rule
			  );


      return seq([many(directive), end_of_input], function(r,_) { return r; })(str);
   };

   
   
   
   return {
      parse : function(taid) {
	 var ta = document.getElementById(taid);
	 var v = (ta.value);
	 console.log(parse_cva(v));
      }
   }

})();