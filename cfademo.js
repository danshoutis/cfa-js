/* Context-free art demo script. */

$(document.body).ready(function() {
   // Make sure canvas works.
   var c = $("#canvas")[0];
   if (!!!c.getContext) {
      $(".controls").hide();
      return;
   }

   // Keep canvas square:
   /*var sz = function() {
      var w = $('#canvas_holder').width();
      var w_adj = 0.8 * w;
      $("#canvas").attr('height',w);
      $("#canvas").attr('width',w);
      $("#canvas")[0].width = w;
      $("#canvas")[0].height = w;
   };
   $(".demo").resize(sz);
   sz();*/

   // Functions for starting and stopping a script:
   var is_running = false;
   var halt_fn = function () {} ;
   var stop = function() {
      if (is_running) {
	 halt_fn() ;
	 is_running = false;
      }
   };

   var start = function() {

      if (is_running) {
	 stop() ;
      }
      $("#cfa_script").blur(); // force value update?
      $("#bbox").blur();
      var bbox = $("#bbox").val().split(",");
      for (var i = 0; i < bbox.length; i++) {
	 bbox[i] = parseFloat(bbox[i]);
      }
      
      console.log($("#cfa_script").val());

      var cfa = CFA.parse('cfa_script');
      is_running = true;
      halt_fn = CFA.exec(cfa, bbox, 'canvas');
   };

   // Hook up buttons:
   $("#b_run").click(function() {
      start();
      $("#b_stop").toggleClass("running");
   });
   
   $("#b_stop").click(function() {
      stop() ; $("#b_stop").toggleClass("running");
   });
   
   $("#b_edit").toggle(function() {
      $("#editor").slideDown('slow');
   },function() {
      $("#editor").slideUp('slow');
   });
   
   // Load predone scripts:
   var mk_script = function(s) {
      var nm = s.children(".name").text();
      var bbx = s.children(".bbox").text();
      var code = s.children(".code").text();
      var ldr = function() {
	 $("#cfa_script").val(code);
	 $("#bbox").val(bbx);
	 stop();
	 start(); 
      };
      return [nm,ldr];
   };

   $(".script").each(function() {
      var v = mk_script($(this));
      var nm = v[0];
      var ldr = v[1];


      var btn = $("<a href='javascript:void(0);'></a>")
	 .text(nm)
	 .click(ldr);

      $("#premade").append($("<li/>").append(btn));
   });


   // Auto-start!
   var x = mk_script($("#auto-start"))[1];
   x();
});