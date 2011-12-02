<%@ page language="java" contentType="text/html; charset=ISO-8859-1"
    pageEncoding="ISO-8859-1"%>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=ISO-8859-1">
<title>Wocket - Review Data Check</title>
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
	
	
	<link href="http://ajax.googleapis.com/ajax/libs/jqueryui/1.8/themes/base/jquery-ui.css" rel="stylesheet" type="text/css"/>
  <script src="http://ajax.googleapis.com/ajax/libs/jquery/1.5/jquery.min.js"></script>
  <script src="http://ajax.googleapis.com/ajax/libs/jqueryui/1.8/jquery-ui.min.js"></script>

<style type="text/css">
	html, body {
		width: 100%;
		height: 100%;
		margin: 0px;
		padding: 0px;
	}
input.btn { 
	  color:#050; 
	  font: bold 84% 'trebuchet ms',helvetica,sans-serif;
	  height: 40px;width:25%;
	}
input.WrongBtn { 
	  color:#F76060; 
	  font: bold 84% 'trebuchet ms',helvetica,sans-serif;
	  height: 40px;width:25%;
	}
	 
	

#reviewer-links {border: 1px silver solid; width:100% ;background-color: #B2AFAF;}
#reviewer-links ul {list-style: none; margin: 0; padding: 5px;}
#reviewer-links li {display: inline; width: 150px;}
#reviewer-links a { margin: 0; padding-top: 2px; padding-bottom: 2px;  padding-left: 10px; padding-right: 10px}

#reviewer-links ul {list-style: none;}
#reviewer-links a {text-align: center; font-weight: bold; text-decoration: none;}
#reviewer-links a:hover {color: #ffcc00; border: solid 1px #ffcc00;}

#checklist li
{
display: inline-block;
list-style-type: none;
padding-right: 20px;
}

/*for action dialouge*/
.actionDivBtn { 
	  color:#050; 
	  font: bold 84% 'trebuchet ms',helvetica,sans-serif;
	  height: 40px;width:95%;
	}
.actionDivtextarea{
	overflow: scroll;
	overflow-y: scroll;
	overflow-x: hidden;
	overflow:-moz-scrollbars-vertical;
}

#actionDiv{background-color: #E6F4F7;}	

</style>

<script type="text/javascript">
var dhxLayout;
var studygrid;
var participantGrid;
var calendar;
function doOnLoad() {
	//dhtmlx layout init
	dhxLayout = new dhtmlXLayoutObject(document.getElementById("layout"), "2U");
	dhxLayout.cont.obj._offsetTop = 70;//55
	dhxLayout.cont.obj._offsetHeight = -30;
	dhxLayout.setSizes();
	dhxLayout.cells("a").setWidth(300);
	dhxLayout.cells("a").setText("<span style='color:#00107A;font-weight:bold;'>Select</span>");

	var tittleStyle = 'display:block; background-color:#01000F; color:#FFFFFF; font-weight:bold;';
	dhxLayout.cells("b").setText("<span style="+tittleStyle+">Check Participant Data</span>");
	dhxLayout.setCollapsedText("a", "Select");
	dhxLayout.setCollapsedText("b", "Check Participant Data");
	
	//init left inner Layout
	leftInnerLayout = dhxLayout.cells("a").attachLayout("2E");
	
	dhxLayout.cells("a").showHeader();//show header of left outer cell
	//set all cell height re-size false
	leftInnerLayout.cells("a").fixSize(false, true);
	leftInnerLayout.cells("b").fixSize(false, true);
	
	

	//set cells title 
	leftInnerLayout.cells("a").setText("<span style="+tittleStyle+">Select Study</span>");
	leftInnerLayout.cells("b").setText("<span style="+tittleStyle+">Select Participant</span>");
	leftInnerLayout.setCollapsedText("a", "Select Study");
	leftInnerLayout.setCollapsedText("b", "Select Participant");
	
	
	//attach div grid object to each left inner layout cells
	studygrid = leftInnerLayout.cells("a").attachGrid();
	participantGrid = leftInnerLayout.cells("b").attachGrid();
	intiGrid(studygrid,"study","reviewerGetAssignedStudy.html",true);
	intiGrid(participantGrid,"participant","",false);
	//attach calendar div
	
	dhxLayout.cells("b").attachObject("rightPanel");
	
	studygrid.attachEvent("onRowSelect",studyGridOnRowClick);

	participantGrid.attachEvent("onRowSelect",participantGridOnRowClick);
			
	//init calendar
	initCalendar();
	
// 	dhxLayout.attachEvent("onPanelResizeFinish", function(){
// 		getChart();
// 	});

// 	dhxLayout.attachEvent("onCollapse", function(a){
// 		getChart();
// 	});
// 	dhxLayout.attachEvent("onExpand", function(a){
// 		getChart();
// 	});
	
}

function initCalendar()
{
	calendar = new dhtmlXCalendarObject(["fromDate"]);//attached calander object to text fields startDate and endDate
	calendar.hideTime();
	var dt = calendar.getDate("%Y-%m-%d");
	document.getElementById("fromDate").value = dt;
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

//study grid row onCilck event
function studyGridOnRowClick(rowID)
{
	participantGrid.clearAll();
	var studyId = studygrid.cellById(rowID,0).getTitle();
	url = "reviewerGetStudyParticipants.html?studyId="+studyId;
	participantGrid.load(url,"json");
	document.getElementById("dataCheckDiv").style.display = "none"
	displayMessageDiv("Please Select Participant");
}

//participant grid row onClick event
function participantGridOnRowClick(rowID)
{
	if(document.all){//check browser because getting problem in firefox and in IE
		 document.getElementById("pId").innerText = participantGrid.cellById(rowID,0).getTitle();
		 document.getElementById("fName").innerText = participantGrid.cellById(rowID,1).getTitle();
		 document.getElementById("lName").innerText = participantGrid.cellById(rowID,2).getTitle();
	} else{
		 document.getElementById("pId").textContent = participantGrid.cellById(rowID,0).getTitle();
		 document.getElementById("fName").textContent = participantGrid.cellById(rowID,1).getTitle();
		 document.getElementById("lName").textContent = participantGrid.cellById(rowID,2).getTitle();
	   	}

 //var dt = Calendar.getDate("%Y-%m-%d");
 // document.getElementById("date").value = dt;
//$("#chartContainer").html("");
  hideMessageDiv();
  //getChart();
  getAssignedChecklist();
}


//display message div
function displayMessageDiv(messg)
{
	 // document.getElementById("chartDiv").style.display = "none";//hide chart
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
	  document.getElementById("dataCheckDiv").style.display = "";//show chart
 }
 
 //AJAX to get study Checklist
 function getAssignedChecklist()
 {
	 rowId = studygrid.getSelectedId();
	 if(rowId)
	 {
		 var studyId = studygrid.cellById(rowId,0).getTitle();
		 var xmlHttp = getAjaxGETRequest();
	  		xmlHttp.onreadystatechange=function()
	  	  	{
	  	  		if (xmlHttp.readyState==4 && xmlHttp.status==200)
	  	    	{
	  	  			var assignedCheck = eval(xmlHttp.responseText);//get Id from server
	  	  		    addChecklistCheckBox(assignedCheck);
	  	    	}
	  	  	}
	  		xmlHttp.open("GET","getStudyCheckList.html?studyId="+studyId,true);
	  		xmlHttp.send(); 
	 }
	 else
		 alert("Please select study first.")
 }
 
 //add checklist for study
function addChecklistCheckBox(assignedCheck)
{
	 var ul = document.getElementById("checklist");
	 ul.innerHTML = "";
	 for(var i=0; i<assignedCheck.length; i++)
	 {
		var check =  assignedCheck[i];
		var new_li = document.createElement('li');
		
		var checkBox = document.createElement('input');
		checkBox.type= "checkbox";
		checkBox.value = check[0];
		checkBox.name = "checkGroup";
		checkBox.onclick = function(){checkBoxOnclick()};
		
		var checkLabel = document.createElement('label');
		if(document.all)//check browser because getting problem in firefox and in IE
			checkLabel.innerText = check[1];
		else
			checkLabel.textContent = check[1];
		new_li.appendChild(checkBox);
		new_li.appendChild(checkLabel);
		
		ul.appendChild(new_li);
		
	}
}
 
function checkBoxOnclick()
{
 	var checkBoxs = document.getElementsByName("checkGroup");
 	var disable = true;
 	for(var i=0; i<checkBoxs.length;i++)
 	{
 		var check = checkBoxs[i];
 		if(!check.checked)
 		{
 			disable = true;
 			break;
 		}
 		else
 			disable = false;
 	}
 	
 	document.getElementById("everyThingOkBtn").disabled = disable;
	document.getElementById("okButBtn").disabled = disable;
	document.getElementById("wrongBtn").disabled = disable;
}
 
 //open Action Window
function openActionWindow()
 {
// 	 var pId = participantGrid.cellById(participantGrid.getSelectedId(),0).getTitle();
// 	 var url = "DataCheckAction.html?pId="+pId;
// 	 var left = (screen.width/2);
// 	 var top = (screen.height/2);
// 	 window.open(url, 'ActionWindow', 'width=300,height=600,left='+left+',top='+top+',toolbar=0,status=0,directories=0,menubar=0');

// document.getElementById("dataCheckDiv").style.zIndex = "1";
// document.getElementById("dataCheckDiv").style.position ="absolute"; 
// document.getElementById("actionDiv").style.display= "";
// document.getElementById("actionDiv").style.position ="absolute";
// document.getElementById("actionDiv").style.zIndex = "2";
$("#actionDiv").dialog({ width: 340,resizable: false,title: '<b>Take Action</b>'});


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
<h2>Check Participant Data</h2>


<div id="layout">
<br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/>
<br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/>
</div>

<div id="assignedStudy_Container" style="width:100%;height:100%;"></div>


<div id="participant_Container" style="width:100%;height:100%;"></div>

<!-- Right Panel -->
<div id="rightPanel" style="width: 100%;height: 100%;overflow: auto;">

	<div id="mssg" style="width: 50%;margin-left: auto;margin-right: auto;margin-top: 25%;">
		<fieldset>
			<legend>Message:</legend>
			<center><h4 id="mssgText">Please Select Study</h4></center>
		</fieldset>
	</div>

	<!-- right div for data check -->
	<div id="dataCheckDiv" style="display: none;">
		<b><label>Participant:</label></b>
		<table border="1" cellspacing="1px">
		<tr>
			<th>Participant Id</th><th>First Name</th><th>Last Name</th>
		</tr>
		<tr>
			<td id="pId"></td><td id="fName"></td><td id="lName"></td>
		</tr>
		</table>
		<hr/>
		<label style="margin-left: 3%;"><b>Show data from last </b></label>
		<select id="dateSelect">
			<option value="">--Select--</option>
			<option value="1D">1 Day</option>
			<option value="1W">1 Week</option>
			<option value="2W">2 Week</option>
			<option value="1M">1 Month</option>
		</select>
		<label><b>Since</b></label><input type="text" id="fromDate" readonly="readonly" style="background-color: #D9D9D9;"/>
	
		<br/>
		<input type="checkbox" id="autoScale" name="autoScale" onclick="autoScaleY(this)" style="margin-left: 3%;"/>Enable Y-axis auto scaling
		
		<center><div id="chartDiv" style="height: 350px;width: 95%;border: 1px solid black;"></div></center>

		<h4 style="margin-left: 3%;">Reviewer Checklist</h4>
		<center>
			<div id="checklistDiv" style="width: 95%;border; border: 1px double black;">
			<ul id="checklist"></ul>
			<input type="button" class="btn" id="everyThingOkBtn" value="Everything OK.
Verified" disabled="disabled" title="Checked all above check box to proceed"/>
			<input type="button" class="btn" id="okButBtn" value="Everything OK, but..
Verified with note attached " disabled="disabled" title="Checked all above check box to proceed"/>
			<input type="button" class="WrongBtn" id="wrongBtn" value="Something's Wrong!
Take action " onclick="openActionWindow();" disabled="disabled" title="Checked all above check box to proceed"/>
			<br/><br/>
			</div>
		</center>
	
	</div><!-- close dataCheck Div -->
	
	
	</div><!-- Close rightPanel Div -->
	
	<!-- action Div open in Dialouge using JQuery -->
	<div id="actionDiv" style="display: none;border: 1px solid black;">
	<h5 style="margin-bottom: 1px;">Participant <label id="actionPId"></label>: Something's Wrong</h5>
	<label>Note:</label><br/>
	<textarea rows="6" cols="32" id="note" name="note" class="actionDivtextarea">Write note.</textarea>
	<br/>
	<label>Take Action:</label>
	<div style="height: 370px;width: 95%;border: 1px solid black;">
		<center>
			<div style="height: 200px;width: 97%;border: 1px solid black;margin-top: 4px;">
				<input type="button" value="  App Update  "/><input type="button" value="  App Restart  "/>
				<br/><br/>
				<textarea rows="6" cols="27" id="pSMSEmail" name="pSMSEmail" class="actionDivtextarea">Send SMS/Email to participant.</textarea>
				<input type="button" value="   Send SMS   "/><input type="button" value="  Send Email  "/>
			</div>

			<div style="height: 155px;width: 97%;border: 1px solid black;margin-top: 4px;">
				<textarea rows="6" cols="27" id="teamSMSEmail" name="teamSMSEmail" class="actionDivtextarea">Send email to research team.</textarea>
				<input type="button" value="Send Email To Research Team"/>
			</div>
		</center>
		<br/>
		<label>Recheck data in:</label>
		<select>
			<option value="">--Select--</option>
			<option value="12hr">12 hours</option>
			<option value="24hr">24 hours</option>
			<option value="2day">2 days</option>
			<option value="5day">5 days</option>
			<option value="7day">1 week</option>
		</select>
		<br/><br/>
		<center>
			<input type="button" class="actionDivBtn" value="Finish Reviewing
Verified"/></center>
<br/>
	</div>

</div><!-- Close actionDiv -->
	





</body>
</html>