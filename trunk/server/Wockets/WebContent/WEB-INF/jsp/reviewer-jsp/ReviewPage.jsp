<%@ page language="java" contentType="text/html; charset=ISO-8859-1"
    pageEncoding="ISO-8859-1"%>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=ISO-8859-1">
<title>Wockets - Manage Participant</title>

	<link rel="stylesheet" type="text/css" href="dhtmlx/dhtmlxLayout/codebase/dhtmlxlayout.css">
	<link rel="stylesheet" type="text/css" href="dhtmlx/dhtmlxLayout/codebase/skins/dhtmlxlayout_dhx_skyblue.css">
	<script src="dhtmlx/dhtmlxLayout/codebase/dhtmlxcommon.js"></script>
	<script src="dhtmlx/dhtmlxLayout/codebase/dhtmlxcontainer.js"></script>
	<script src="dhtmlx/dhtmlxLayout/codebase/dhtmlxlayout.js"></script>
	<link rel="stylesheet" type="text/css" href="dhtmlx/dhtmlxCalendar/codebase/dhtmlxcalendar.css"></link>
	<link rel="stylesheet" type="text/css" href="dhtmlx/dhtmlxCalendar/codebase/skins/dhtmlxcalendar_dhx_skyblue.css"></link>
	<script src="dhtmlx/dhtmlxCalendar/codebase/dhtmlxcalendar.js"></script>
	
	<script type="text/javascript" src="http://ajax.googleapis.com/ajax/libs/jquery/1.6.1/jquery.min.js"></script>
	<script type="text/javascript" src="js/highStockChart/highstock.js"></script>
	<script type="text/javascript" src="js/highStockChart/dark-green.js"></script>
	
	<script type="text/javascript" src="js/highStockChart/exporting.js"></script>
	<script type="text/javascript" src="js/highStockChart/reviewGraph.js"></script>
<style type="text/css">
	html, body {
		width: 100%;
		height: 100%;
		margin: 0px;
		padding: 0px;
	}
	

#reviewer-links {border: 1px silver solid; width:100% ;background-color: #B2AFAF;}
#reviewer-links ul {list-style: none; margin: 0; padding: 5px;}
#reviewer-links li {display: inline; width: 150px;}
#reviewer-links a { margin: 0; padding-top: 2px; padding-bottom: 2px;  padding-left: 10px; padding-right: 10px}

#reviewer-links ul {list-style: none;}
#reviewer-links a {text-align: center; font-weight: bold; text-decoration: none;}
#reviewer-links a:hover {color: #ffcc00; border: solid 1px #ffcc00;}

</style>
	
	<script>
	var dhxLayout;
    var studygrid;
    var participantGrid;
	var Calendar;
	var leftInnerLayout;
	var chart;
	function doOnLoad() {
		//dhtmlx layout init
		dhxLayout = new dhtmlXLayoutObject(document.getElementById("layout"), "2U");
 		dhxLayout.cont.obj._offsetTop = 70;//55
		dhxLayout.cont.obj._offsetHeight = -30;
 		dhxLayout.setSizes();
 		dhxLayout.cells("a").setWidth(300);
 		dhxLayout.cells("a").setText("<span style='color:#00107A;font-weight:bold;'>Select</span>");

		var tittleStyle = 'display:block; background-color:#01000F; color:#FFFFFF; font-weight:bold;';
 		dhxLayout.cells("b").setText("<span style="+tittleStyle+">Study Graph</span>");
 		dhxLayout.setCollapsedText("a", "Select");
		dhxLayout.setCollapsedText("b", "Study Graph");
		
		//init left inner Layout
		leftInnerLayout = dhxLayout.cells("a").attachLayout("3E");
		
		dhxLayout.cells("a").showHeader();//show header of left outer cell
		//set all cell height re-size false
		leftInnerLayout.cells("a").fixSize(false, true);
		leftInnerLayout.cells("b").fixSize(false, true);
		leftInnerLayout.cells("c").fixSize(false, true);
		

		//set cells title 
		leftInnerLayout.cells("a").setText("<span style="+tittleStyle+">Select Study</span>");
		leftInnerLayout.cells("b").setText("<span style="+tittleStyle+">Select Participant</span>");
		leftInnerLayout.cells("c").setText("<span style="+tittleStyle+">Select Date</span>");
		leftInnerLayout.setCollapsedText("a", "Select Study");
		leftInnerLayout.setCollapsedText("b", "Select Participant");
		leftInnerLayout.setCollapsedText("c", "Select Date");
		
		//attach div grid object to each left inner layout cells
		studygrid = leftInnerLayout.cells("a").attachGrid();
		participantGrid = leftInnerLayout.cells("b").attachGrid();
		intiGrid(studygrid,"study","reviewerGetAssignedStudy.html",true);
		intiGrid(participantGrid,"participant","",false);
		//attach calendar div
		leftInnerLayout.cells("c").attachObject("calendar");
		
		
		dhxLayout.cells("b").attachObject("rightPanel");
		
		studygrid.attachEvent("onRowSelect",studyGridOnRowClick);

		participantGrid.attachEvent("onRowSelect",participantGridOnRowClick);
				
		//init calendar
		initCalendar();
		
		dhxLayout.attachEvent("onPanelResizeFinish", function(){
			getChart();
		});

		dhxLayout.attachEvent("onCollapse", function(a){
			getChart();
			//onExpandOrCollapseChart();
		});
		dhxLayout.attachEvent("onExpand", function(a){
			getChart();
			//onExpandOrCollapseChart();
		});
		
 }
	
    function intiGrid(grid,type,url,loadBool)
    { 
    	grid.setImagePath("dhtmlx/imgs/");
    	switch (type) {
		case 'study':
			grid.setHeader("Study Id,Description");
	    	grid.setInitWidths("100,*");
	    	grid.setColAlign("left,left");
			grid.setColSorting("str,str");
	    	grid.setColTypes("ro,ro");
			break;
		case 'participant':
			grid.setHeader("Participant Id,First Name,Last Name");
    		grid.setInitWidths("100,100,*");
    		grid.setColAlign("left,left,left");
			grid.setColSorting("str,str,str");
    		grid.setColTypes("ro,ro,ro");
    		break;
		}
    	grid.setSkin("light");
    	grid.init();
    	if(loadBool)
    		grid.load(url,"json");
    }
    
    function initCalendar()
    {
    	Calendar = new dhtmlXCalendarObject("calendar");
    	Calendar.attachEvent("onClick",calanderOnClick);
    	Calendar.hideTime();
    	Calendar.show();
    }
    
    //***************Study Grid************
        //study grid row onClick event
    function studyGridOnRowClick(rowID)
    {
    	participantGrid.clearAll();
    	var studyId = studygrid.cellById(rowID,0).getTitle();
    	url = "reviewerGetStudyParticipants.html?studyId="+studyId;
    	participantGrid.load(url,"json");
    	clearFlagDetail();
    	displayMessageDiv("Please Select Participant");
    }
    
  //***************Participant Grid************
    //participant grid row onClick event
    function participantGridOnRowClick(rowID)
    {
	 document.getElementById("pId").value = participantGrid.cellById(rowID,0).getTitle();
	  var dt = Calendar.getDate("%Y-%m-%d");
	  document.getElementById("date").value = dt;
  	  $("#chartContainer").html("");
	  hideMessageDiv();
	  getChart();
    }
  
  //display message div
  function displayMessageDiv(messg)
  {
	  document.getElementById("chartDiv").style.display = "none";//hide chart
	  document.getElementById("mssg").style.display = "";
	  if(document.all){//check browser because getting problem in firefox and in IE
		  	document.getElementById("mssgText").innerText = messg;
		} else{
		    document.getElementById('mssgText').textContent = messg;
		}
   }
  //hide message div
  function hideMessageDiv()
  {
	  document.getElementById("mssg").style.display = "none";
	  document.getElementById("chartDiv").style.display = "";//show chart
   }
  
  //*********calander onClick event***
  function calanderOnClick()
  {
	  var pId = document.getElementById("pId").value;
	  if(pId =="")
		{
		  	alert("Please select participant first.");
		  	return;
		}
	  var dt = Calendar.getDate("%Y-%m-%d");
	  document.getElementById("date").value = dt;
	  getChart();

}
 //************chart create******* 
	//Create chart & resize chart size based on Layout cell 'b'
	function getChart()
	{
		document.getElementById("loadingDiv").style.display = "";
	 	clearFlagDetail();//clear all falg details
	 	var width = dhxLayout.cells("b").getWidth();
		document.getElementById("chartContainer").style.width = (width*0.9);//set chart width 90% of the cell b width	
	 	var pId = document.getElementById("pId").value;
		var date = document.getElementById("date").value;
		//AJAX for JSON data
		var chartDataJSON = sendAjax(pId,date);
		if(validateChartJSON(chartDataJSON))
			{
				hideMessageDiv();
				chart = createChart("chartContainer",chartDataJSON);//method in "js/highStockChart/reviewGraph.js" file
			}
		 document.getElementById("loadingDiv").style.display = "none";
	}

//validate main JSON object
function validateChartJSON(chartDataJSON)
{
	var result = false;
	var phoneStats = chartDataJSON.phoneStats;
	for(var i=0; i< phoneStats.length; i++)
	{
		if(phoneStats[i].data.length >0 )
		{
			result = true;
			return result;
		}
	}
	
	var heartRateData = chartDataJSON.hrData;
	for(var i=0; i< heartRateData.length; i++)
	{
		if(heartRateData[i].data.length >0 )
		{
			result = true;
			return result;
		}
	}
		
// 	if(chartDataJSON.promptList.data.length >0 || chartDataJSON.smsList.data.length >0 || chartDataJSON.swappedFlag.length > 0 
// 		|| chartDataJSON.wocketData.length >0 || chartDataJSON.noteList.length >0 || chartDataJSON.dataUploadEvent.length >0)
		if(chartDataJSON.promptList.data.length >0 || chartDataJSON.smsList.data.length >0 || chartDataJSON.swappedFlag.data.length > 0 
				|| chartDataJSON.wocketData.length >0 || chartDataJSON.noteList.data.length >0 || chartDataJSON.dataUploadEvent.data.length >0)
		{
			result = true;
			return result;
		}


	if(result == false)
	 {
		displayMessageDiv("No record Found on "+document.getElementById("date").value);
	 	return result;
	 }
}// close validateChartJSON function


//clear all flag detail
function clearFlagDetail()
{
	$('#smsTable').html("");
	$('#swappedTable').html("");
	$('#promptTable').html("");
	$('#noteTable').html("");
}

//autoScale of Y-axis
//autoScale check box click 
function autoScaleY(chkbox)
{
	var autoScale = (chkbox.checked) ? "enable" : "disable";
	var hiddenSerise = chart.get("hidden");
	if(autoScale == "enable")
		hiddenSerise.hide();
	else
		hiddenSerise.show();
}
</script>
</head>
<body onload="doOnLoad();">
<div id="reviewer-links">
<ul>
<li><a href="personalInfo.html">Personal Profile</a></li>
<li><a href="reviewerAssignedStudy.html">Assigned Study</a></li>
<li><a href="reviewerReviewPage.html">Review Participant</a></li>
</ul>
</div>

<div id="layout">
<br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/>
<br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/>

</div>


<div id="assignedStudy_Container" style="width:100%;height:100%;"></div>


<div id="participant_Container" style="width:100%;height:100%;"></div>



<div id="calendar" style="width:100%;height: 100%;position: relative;"></div>



<!-- Right panel -->
<div id="rightPanel" style="width: 100%;height: 100%;overflow: auto;">



<div id="mssg" style="width: 50%;margin-left: auto;margin-right: auto;margin-top: 25%;">
<fieldset>
<legend>Message:</legend>
<center><h4 id="mssgText">Please Select Study</h4></center>
</fieldset>
</div>

<div id="chartDiv" style="display: none;">
<table style="margin-left:2.5%;">
<tr>
<td><label>Participant Id:</label><td><input type="text" name="pId" id="pId" readonly="readonly" style="background-color:#D9D9D9;"/><td>
<td><label>Date:</label><td><input type="text" name="date" id="date" readonly="readonly" style="background-color:#D9D9D9;"/><td>
</tr>
</table>

<br/>
<input type="checkbox" id="autoScale" name="autoScale" onclick="autoScaleY(this)" style="margin-left: 3%;"/><b>Enable Y-axis auto scaling</b>
<center><div id="chartContainer" style=";width: 95%;"></div></center>
</div>

<br/>

<div style="overflow: auto; position: relative;float: left; margin-left: 1%;">
<table id="promptTable" cellspacing=0 cellpadding=2 border="1">
<COL WIDTH=70><COL WIDTH=200>
 </table>
</div>

<div style="overflow: auto; position: relative;float: left; margin-left: 1%;">
<table id="smsTable" cellspacing=0 cellpadding=2 border="1" width=300>
<COL WIDTH=100><COL WIDTH=200>
 </table>
</div>

<div style="overflow: auto;position: relative;float: left;margin-left: 1%;margin-top: 1%;">
<table id="swappedTable" cellspacing=0 cellpadding=2 style="max-width: 250" border="1">
<COL WIDTH=50><COL WIDTH=100>
 </table>
</div>

<div style="overflow: auto;position: relative;float: left;margin-left: 1%;margin-top: 1%;">
<table id="noteTable" cellspacing=0 cellpadding=2 border="1">
<COL WIDTH=50><COL WIDTH=100>
 </table>
</div>



<div id="loadingDiv" style="display: none;">
<center><img alt="loading" src="img/loading.gif"/></center>
</div>


</div><!-- end right panel -->


</body>
</html>