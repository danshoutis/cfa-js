// simplistic eye candy for the good ol' resume
//  see: contextfreeart.org

vect_x_mat = function(v,m) {
   return [v[0] * m[0] + v[0] * m[1] + m[4],
	   v[1] * m[2] + v[1] * m[3] + m[5]];
}





Context = function() { return {
   tx : [1,0,0,1,0,0], /* txformation */
   color : [0,0,0], /* color */
   screenw : 0,
   screenh : 0,
   tx_stack : [],
   color_stack : [],
   push : function() {
      this.color_stack.push(this.color);
      this.tx_stack.push(this.tx);
   },
   pop : function() {
      this.color = this.color_stack.pop();
      this.tx = this.tx_stack.pop();
   }
};
}
Rule = function(body) { /* An l-system rule. */
   
   can_expand = function(view_matrix, screenw, screenh) {
      a = vect_x_mat([0,0],view_matrix)
      b = vect_x_mat([1,1],view_matrix)
      da = b[0] - a[0];
      db = b[1] - a[1];
      
      szsq = (da * da + db * db);
      
      // Too small to expand:
      if (sizesq < 3.0)
	 return; 

      // Offscreen: Dont bother expanding.
      x = Math.min(a[0],b[0]);
      xx = Math.max(a[0],b[0]);
      y = Math.min(a[1],b[1]);
      yy = Math.max(a[1],b[1]);
      if (xx <= 0 ||
	  yy <= 0 ||
	  x >= screenw ||
	  y >= screenh) {
	     return false;
	  }
      return true;
   };

   expand = function(c,rulesdict) {
      res = []
      if (can_expand(c.tx, c.screenw, c.screenh)) {
	 for (x in body) {
	    x.enter(c);
	    expanded = x.expand(c,rulesdict);
	    res.append(expanded);
	    x.exit(c);
	 }
      } else {
	 return [this]; 
      }
   };

   return {
      expand_to : function(view_matrix, screenw, screenh, ruledict) {


	 new_args = []
	 for (a in args) {
	    if (typeof(a) == 'string') {
	       expanded = rules[a](
	    } else {
	       new_args.push(a)
	    }
	 }
      },
      draw : function(ctx) {
	 ctx.save();
	 for (a in args) {
	    if (typeof(a) == 'function') a(ctx);
	 }
	 ctx.restore();
      }
   }

   return {
      matrix : [1,0,0,1,0,0],
      color : [0,0,0],
      draw : function(ctx) {
	 ctx.save();
	 for c in args
	 ctx.transform.apply(ctx, this.matrix);
	 ctx.fillStyle = "rgb(0,0,0)"; // fixme
	 ctx.fillRect(0,0,1,1);
	 ctx.restore();
      },
      bbox : function() {
	 
      }
   }
}

G = (function() {
   var c = document.getElementById("eyecandy");
   var ctx = c.getContext('2d');
   
   var dummy = LS()
   dummy.matrix = [100,0,0,100,10,10];
   
   var draw = function() {
      dummy.draw(ctx);
   }

   draw();

});
