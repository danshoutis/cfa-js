// eye candy for the good ol resume. 
//  see: contextfreeart.org


MAXD=60;

TimeAware = function(inner) {
   // Transform a rule to support expressions-over-time in its args.
   return function() {
      var _this = this;
      var a = arguments;
      var dv = [];
      var haveone = false;;
      for (i = 0; i < a.length; i++) {
	 if (typeof(a[i]) == 'string') {
	    a[i] = new Function(["t"], "return " + a[i] + ";");
	    dv.push(true);
	    haveone = true;
	 } else {
	    dv.push(false);
	 }
      }

      if (!haveone) 
	 return inner.apply(this,arguments);

      return function(c) {
	 var na = [];

	 for (i = 0; i < a.length; i++) {
	    if (dv[i]) {
	       na.push(a[i](c.time));
	    } else { na.push(a[i]); }
	 }
	 var consed = inner.apply(_this,na);
	 return consed(c);
      };
   };
};

Square = function(c) {  c.fillRect(0,0,1,1); };

Tx = TimeAware(function(matrix, inner) {
   var enter = function(c) { c.save(); }
   var exit = function(c) { c.restore(); }
   return function(c) {
      enter(c);
      c.transform(matrix);
      inner(c);
      exit(c);
   };
});

Rot = TimeAware(function(ang, inner) {
   var yv = Math.sin(ang);
   var xv = Math.cos(ang);

   // new x axis = [xv,yv];
   // new y axis = [-yv,xv];
   return Tx([xv,yv,-yv,xv,0,0],inner);
});

Mv = TimeAware(function(x,y,inner) {
   return Tx([1,0,0,1,x,y], inner);
});

Sc = TimeAware(function(xamt,yamt,inner) {
   return Tx([xamt,0,0,yamt,0,0],inner);
});

Rand = function(inners) {
   // Flip a coin. Trick: somehow arrive at a stable number...
};

M = function(inners) {
   return function(ctx) {
      for (i = 0; i < inners.length; i++) {
	 inners[i](ctx);
      }
   };
};

Rule = function(inner) {
   can_expand = function(ctx, view_matrix, screenw, screenh) {
      var a = vect_x_mat([0,0],view_matrix)
      var b = vect_x_mat([1,1],view_matrix)
      var da = b[0] - a[0];
      var db = b[1] - a[1];
      
      var sizesq = (da * da + db * db);

      // Time is less than zero:
      if (ctx.time < 0.0)
	 return;

      // Too small to expand:
      if (sizesq < 3.0)
	 return; 

      // Offscreen: Dont bother expanding.
      var x = Math.min(a[0],b[0]);
      var xx = Math.max(a[0],b[0]);
      var y = Math.min(a[1],b[1]);
      var yy = Math.max(a[1],b[1]);

      if (xx <= 0 ||
	  yy <= 0 ||
	  x >= screenw ||
	  y >= screenh) {
	     return false;
	  }
      return true;
   };

   return function(c) {
      // check recursion depth:

      if (c.tx_stack.length > MAXD)
	 return;

      // check onscreen size:
      if (can_expand(c, c.tx, c.screenw, c.screenh)) {
	 return inner(c);
      }
   };
};

Context = function(ctx,w,h) { return {
   tx : [1,0,0,1,0,0], /* txformation */
   color : [0,0,0], /* color */
   screenw : w,
   screenh : h,
   time : 0.0,
   fillRect : function(x,y,xx,yy) { return ctx.fillRect(x,y,xx,yy); } ,
   tx_stack : [],
   color_stack : [],
   time_stack : [],
   save : function() {
      this.color_stack.push(this.color);
      this.tx_stack.push(this.tx);
      this.time_stack.push(this.time);
      ctx.save();
   },
   restore : function() {
      this.color = this.color_stack.pop();
      this.tx = this.tx_stack.pop();
      this.time = this.time_stack.pop();
      ctx.restore();
   },
   transform : function(mat) {
      this.tx = mat_x_mat(mat, this.tx);
      ctx.transform.apply(ctx,mat);
   }
};
}

Simple = function(ctx) {
   return M([
	     Sc(0.5,1.0,Square),
	     Rot("-1.0 * t * 0.01",Mv(0.0,0.25,Sc(0.95,0.95,Rule(Simple))))
	    ])(ctx);
}

G = (function() {
   var c = document.getElementById("eyecandy");
   var ctx = c.getContext('2d');
   
   var dummy = Tx([100,0,0,100,10,10],Rule(Simple));

   var t = 0.0;
   var interval = (1.0 / 60.0);

   var context = Context(ctx,200,400);
   var draw = function() {
      ctx.fillStyle = "rgb(255,255,255)";
      ctx.fillRect(0,0,200,400);
      ctx.fillStyle = "rgb(0,0,0)";
      t += interval;
      context.time = t;
      dummy(context);
   }

   //setInterval(draw,1000.0 * interval);
   draw();

});
