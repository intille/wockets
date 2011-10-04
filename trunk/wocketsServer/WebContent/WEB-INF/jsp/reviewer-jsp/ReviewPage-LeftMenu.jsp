<%@ page language="java" contentType="text/html; charset=ISO-8859-1"
    pageEncoding="ISO-8859-1"%>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=ISO-8859-1">
<title>reviewPage-LeftMenu</title>
	<link rel="stylesheet" type="text/css" href="dhtmlx/dhtmlxCalendar/codebase/dhtmlxcalendar.css"></link>
	<link rel="stylesheet" type="text/css" href="dhtmlx/dhtmlxCalendar/codebase/skins/dhtmlxcalendar_dhx_skyblue.css"></link>
	<script src="dhtmlx/dhtmlxCalendar/codebase/dhtmlxcalendar.js"></script>
    <script type="text/javascript">
    var studygrid;
    var participantGrid;
	var Calendar;
    function doInit(){
		studygrid = intiGrid("assignedStudy_Container","study","reviewerGetAssignedStudy.html",true);
		studygrid.attachEvent("onRowSelect",studyGridOnRowClick);

		participantGrid = intiGrid("participant_Container","participant","",false);
		participantGrid.attachEvent("onRowSelect",participantGridOnRowClick);
				
		//init calendar
		initCalendar();

    }
    
    function intiGrid(divObj,type,url,loadBool)
    {
    	var grid = new dhtmlXGridObject(divObj);
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
    	return grid;
    }
    
    function initCalendar()
    {
    	Calendar = new dhtmlXCalendarObject("calendar");
    	Calendar.hideTime();
    }
    
    //***************Study Grid************
    function studyGridOnRowClick(rowID)
    {
    	document.getElementById("participantDiv").style .display ="";
    	participantGrid.clearAll();
    	var studyId = studygrid.cellById(rowID,0).getTitle();
    	url = "reviewerGetStudyParticipants.html?studyId="+studyId;
    	participantGrid.load(url,"json");
    }
    
    function participantGridOnRowClick(rowID)
    {
    	Calendar.show();
    }
    </script>

</head>
<body onload="doInit()">
<div id="main-menu" style="width:23%;">
<h4>Select Study:</h4>
<div id="assignedStudy_Container" style="width:98%;height:100px;"></div>

<!-- Participant Div -->
<div id="participantDiv" style="display: none;">
<h4>Select Participant:</h4>
<div id="participant_Container" style="width:98%;height:150px;"></div>


<!-- calendar div -->
<div id="calendar" style="width:50%;height: 200px;position: relative;"></div>

</div>

</div>


</body>
</html>