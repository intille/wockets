<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
 <script type="text/javascript" src="FusionCharts.js">
    </script>
</head>
<body>
<!--<div style="position:absolute; top: 0px; left: 0px;width:100px;height:100px; z-index: 1;"><img src="images/backcolor.gif" /></div>-->
<div id="chartContainer"  style="position:absolute; top: 0px; left: 0px; z-index: 0;">
<!--FusionCharts will load here!-->
</div>          

    <script type="text/javascript"><!--         

	  var myChart = new FusionCharts( "ZoomLine.swf", 
      "myChartId", "800", "500", "0", "1" );
	  myChart.setXMLUrl("Data.php?<?php echo $_SERVER['QUERY_STRING'];?>");     
      myChart.setTransparent(true);
      myChart.render("chartContainer");
	  
    </script>
</body>
</html>
