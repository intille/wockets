<%@ page language="java" contentType="text/html; charset=ISO-8859-1"
    pageEncoding="ISO-8859-1"%>
    <%@taglib uri="http://www.springframework.org/tags/form" prefix="form"%>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=ISO-8859-1">
<title>Wocket - Manage Participant</title>
<title>Wockets - New Participant</title>
	<link rel="stylesheet" type="text/css" href="dhtmlx/dhtmlxCalendar/codebase/dhtmlxcalendar.css"></link>
	<link rel="stylesheet" type="text/css" href="dhtmlx/dhtmlxCalendar/codebase/skins/dhtmlxcalendar_dhx_skyblue.css"></link>
	<script src="dhtmlx/dhtmlxCalendar/codebase/dhtmlxcalendar.js"></script>
<style type="text/css">
.mandatory{
color:#ff0000;
}
</style>

<script type="text/javascript">
var fName,lName,gender,email,bDate, height, weight,race,tzone,personalNotes;
var assignedPhoneGrid;
var availabelPhoneGrid;
var assignedSimGrid;
var availabelSimGrid;
var assignedWocketGrid;
var availWocketGrid;
var selectedWocketGrid;

function doOnLoad() {
	//store all value to global variable
	fName = document.getElementById("fName").value;
	lName = document.getElementById("lName").value;
	gender = document.getElementById("gender").value;
	email = document.getElementById("email").value;
	bDate = document.getElementById("birthDate").value;
	height = document.getElementById("height").value;
	weight = document.getElementById("weight").value;
	race = document.getElementById("race").value;
	tzone = document.getElementById("utcOffset").value;
	personalNotes = document.getElementById("personalNotes").value;
	
	//init dhtmlx calendar
	var calendar = new dhtmlXCalendarObject(["birthDate"]);//attached calander object to text fields birthDate
	calendar.hideTime();
	//set all personal detail field as readonly
	personalFieldStyle(true,'#D9D9D9');
	assignedPhoneGrid = GridInit('phoneGrid_Container','assignedPhone','getPartAssignedPhone.html');//init Assigned phone grid
	
	availabelPhoneGrid = GridInit('avialPhGrid_Container','availablePhone','getAvailPhoneDirectory.html');//init availabel phone grid
	availabelPhoneGrid.attachEvent("onRowSelect",availabelPhRowOnClick);
	
	assignedSimGrid = GridInit('simGrid_Container','assignedSim','getPartAssignedSim.html');//init Assigned sim grid
	
	availabelSimGrid = GridInit('avialSimGrid_Container','availabelSim','getAvailableSimcardList.html');//init availabel sim grid
	availabelSimGrid.attachEvent("onRowSelect",availabelSimRowOnClick);
	
	assignedWocketGrid = GridInit('wocketGrid_Container','assignedWockets','getPartAssignedWocket.html');//init assigned wocket grid
	
	availWocketGrid = GridInit('availWocketgrid_container','availWockets','getAvailableWocketList.html');//init availabel wocket grid
	availWocketGrid.attachEvent("onRowSelect",availWocketGridRowOnClick);//attached event to avail wockets grid
	
	selectedWocketGrid = GridInit('selectedWocketGrid_container','assignedWockets','');//init availabel wocket grid
	
	
}

//sex radio button click event
function sexRadionBttClick(radioValue)
{
	document.getElementById("gender").value = radioValue;
}

//UTC offset combo box select event
function setComboBoxValue(selectValue,dest)
{
	if(selectValue !="")
		document.getElementById(dest).value = selectValue;
}

function personalFieldStyle(readOnly,color)
{
	document.getElementById("fName").readOnly = readOnly;
	document.getElementById("lName").readOnly = readOnly;
	document.getElementById("email").readOnly = readOnly;
	document.getElementById("height").readOnly = readOnly;
	document.getElementById("weight").readOnly = readOnly;
	document.getElementById("personalNotes").readOnly = readOnly;
	
 	document.getElementById("fName").style.background= color;
	document.getElementById("lName").style.background= color;
	document.getElementById("email").style.background= color;
	document.getElementById("height").style.background= color;
	document.getElementById("weight").style.background= color;
	document.getElementById("personalNotes").style.background= color;

	document.getElementById("utc_offsetCombo").disabled = readOnly;
	document.getElementById("sexM").disabled = readOnly;
	document.getElementById("sexF").disabled = readOnly;
	document.getElementById("raceCombo").disabled = readOnly;
}

//personal detail No radio button click
function personalRadioButtNo()
{
	personalFieldStyle(true,'#D9D9D9');
	resetAllPersonalValues();
	document.getElementById("personalSubmitBttn").disabled = true;//disable submit button
}
//personal detail Yes radio button click
function personalRadioButtYes()
{
	personalFieldStyle(false,'#FCFCFC');
	document.getElementById("personalSubmitBttn").disabled = false;//enable submit button
}

function resetAllPersonalValues()
{
	document.getElementById("fName").value = fName;
	document.getElementById("lName").value = lName;
	document.getElementById("email").value = email;
	document.getElementById("height").value = height;
	document.getElementById("weight").value = weight;
	document.getElementById("personalNotes").value = personalNotes;
	document.getElementById("birthDate").value = bDate;
	document.getElementById("gender").value = gender;
	document.getElementById("race").value = race;
	document.getElementById("utcOffset").value = tzone;
}

//Submit Update personal Info Form
function updatePersonalInfoSubmit()
{
document.personalInfoForm.submit();
}


//*************Grid Init***************
//init grid
function GridInit(divObj,type,loadUrl)
{
	Grid = new dhtmlXGridObject(divObj);//create grid object
	Grid.setImagePath("dhtmlx/imgs/");

switch (type) {
case 'assignedPhone':
		Grid.setHeader("IMEI,Phone Model,Platform,OS Version,App Version,Is Active,Inactive Reason");
		Grid.setInitWidths("110,110,90,90,90,80,*");
		Grid.setColAlign("left,left,left,left,left,left,left");
		Grid.setColSorting("str,str,str,str,str,str,str");
		Grid.setColTypes("ro,ro,ro,ro,ro,ro,ro");
		break;
case 'availablePhone':
		Grid.setHeader("IMEI,Phone Model,Platform,OS Version,App Version,Is Assigned");
		Grid.setInitWidths("120,120,100,100,100,*");
		Grid.setColAlign("left,left,left,left,left,left");
		Grid.setColSorting("str,str,str,str,str,str");
		Grid.setColTypes("ro,ro,ro,ro,ro,ro");
		break;
case 'assignedSim':
		Grid.setHeader("Phone Number,Carrier,Expiration Date,Notes,Is Active,Inactive Reason");
		Grid.setInitWidths("100,100,100,150,100,*");
		Grid.setColAlign("left,left,left,left,left,left");
		Grid.setColSorting("str,str,str,str,str,str");
		Grid.setColTypes("ro,ro,ro,ro,ro,ro");
		break;
case 'availabelSim':
		Grid.setHeader("Phone Number,Carrier,Expiration Date,Is Assigned,Notes");
		Grid.setInitWidths("100,100,100,100,*");
		Grid.setColAlign("left,left,left,left,left");
		Grid.setColSorting("str,str,str,str,str");
		Grid.setColTypes("ro,ro,ro,ro,ro");
		break;
case 'assignedWockets':
		Grid.setHeader("Mac Id,Color Set,Hardware Version,Firmware Version,Printed Id,Notes");
		Grid.setInitWidths("100,100,100,100,100,*");
		Grid.setColAlign("left,left,left,left,left,left");
		Grid.setColSorting("str,str,str,str,str,str");
		Grid.setColTypes("ro,ro,ro,ro,ro,ro");
		break;
case 'availWockets':
		Grid.setHeader("Mac Id,Color Set,Hardware Version,Firmware Version,Printed Id,Is Assigned,Notes");
		Grid.setInitWidths("100,100,100,100,100,100,*");
		Grid.setColAlign("left,left,left,left,left,left,left");
		Grid.setColSorting("str,str,str,str,str,str,str");
		Grid.setColTypes("ro,ro,ro,ro,ro,ro,ro");
		break;
}
	Grid.setSkin("light");
	Grid.init();
	Grid.load(loadUrl,"json");
	return Grid;
}


//*********Phone Detail******************

//new Phone Grid Row onClick event
function availabelPhRowOnClick(rowID)
{
	document.getElementById("newPhIMEI").value = availabelPhoneGrid.cellById(rowID,0).getTitle();
	document.getElementById("newPhModel").value = availabelPhoneGrid.cellById(rowID,1).getTitle();
	document.getElementById("newPhPlatform").value = availabelPhoneGrid.cellById(rowID,2).getTitle();
	document.getElementById("newPhOSVersion").value = availabelPhoneGrid.cellById(rowID,3).getTitle();
	document.getElementById("newPhAppVersion").value = availabelPhoneGrid.cellById(rowID,4).getTitle();
	//Enable Assign New Phone Button
	document.getElementById("assgNewPhBttn").disabled = false;
}


function submitAssignNewPh()
{
	if(availabelPhoneGrid.getSelectedRowId())
	{
		if(document.getElementById("assignReason").value != "")
		{
			var url = "assignNewPhone.html?IMEI="+document.getElementById("newPhIMEI").value+"&reason="+document.getElementById("assignReason").value;
			var xmlHttp = getAjaxGETRequest();
			xmlHttp.onreadystatechange=function()
			{
				if (xmlHttp.readyState==4 && xmlHttp.status==200)
					{
						//refreshPhonesGrid();
						refreshGrid(assignedPhoneGrid,availabelPhoneGrid,"getPartAssignedPhone.html","getAvailPhoneDirectory.html");
					}
			}
			xmlHttp.open("GET",url,true);
			xmlHttp.send();
			document.getElementById("assgNewPhBttn").disabled = true;
		}
		else
			createErrorLabel("Please select reason of assign new phone.",document.getElementById("newPhErrorDiv"),'newPhErrorLabel');
	}
	else
			createErrorLabel("Please select phone from table to assign.",document.getElementById("newPhErrorDiv"),'newPhSelectErrorLabel');
}


function refreshGrid(assignedGrid,availableGrid,assignedUrl,availabelUrl)
{
	assignedGrid.selectAll();
	assignedGrid.deleteSelectedItem();
	availableGrid.selectAll();
	availableGrid.deleteSelectedItem();
	assignedGrid.load(assignedUrl,"json");
	availableGrid.load(availabelUrl,"json");
	
}

//********************Sim card Detail
function availabelSimRowOnClick(rowID)
{
	document.getElementById("newSimPhoneNbr").value = availabelSimGrid.cellById(rowID,0).getTitle();
	document.getElementById("newSimCarrier").value = availabelSimGrid.cellById(rowID,1).getTitle();
	document.getElementById("newSimcontExpDate").value = availabelSimGrid.cellById(rowID,2).getTitle();
	document.getElementById("newSimNote").value = availabelSimGrid.cellById(rowID,4).getTitle();
	
	//Enable Assign New Phone Button
	document.getElementById("assgNewSimBttn").disabled = false;
}

function submitAssignNewSim()//
{
	if(availabelSimGrid.getSelectedRowId())
	{
		if(document.getElementById("assignSimReason").value != "")
		{
			var url = "assignNewSim.html?phoneNbr="+document.getElementById("newSimPhoneNbr").value+"&reason="+document.getElementById("assignSimReason").value;
			var xmlHttp = getAjaxGETRequest();
			xmlHttp.onreadystatechange=function()
			{
				if (xmlHttp.readyState==4 && xmlHttp.status==200)
					{
						refreshGrid(assignedSimGrid,availabelSimGrid,"getPartAssignedSim.html","getAvailableSimcardList.html");
					}
			}
			xmlHttp.open("GET",url,true);
			xmlHttp.send();
			document.getElementById("assgNewSimBttn").disabled = true;
		}
		else
			createErrorLabel("Please select reason of assign new Sim card.",document.getElementById("newSimErrorDiv"),'newSimErrorLabel');
	}
	else
			createErrorLabel("Please select Sim card from table to assign.",document.getElementById("newSimErrorDiv"),'newSimSelectErrorLabel');

}

//************Wockets Detail******************
function availWocketGridRowOnClick(rowID)
{
	document.getElementById("addWocketToList").disabled = false;	//Enable Add to list Button
	document.getElementById("newWocketId").value = availWocketGrid.cellById(rowID,0).getTitle();
	document.getElementById("newColorSet").value = availWocketGrid.cellById(rowID,1).getTitle();
	document.getElementById("newHardwareVersion").value = availWocketGrid.cellById(rowID,2).getTitle();
	document.getElementById("newFirmwareVersion").value = availWocketGrid.cellById(rowID,3).getTitle();
	document.getElementById("newPrinted_Id").value = availWocketGrid.cellById(rowID,4).getTitle();
	document.getElementById("newWocketNote").value = availWocketGrid.cellById(rowID,6).getTitle();
}

//addWocketToList onClick event ---add wocket to selected List
function addWocketToList()
{
	if(availWocketGrid.getSelectedRowId())
	{
	var nbrRows = selectedWocketGrid.getRowsNum();
	selectedWocketGrid.addRow(nbrRows+1,[document.getElementById("newWocketId").value,document.getElementById("newColorSet").value,
	                                     document.getElementById("newHardwareVersion").value,document.getElementById("newFirmwareVersion").value,
	                                     document.getElementById("newPrinted_Id").value,document.getElementById("newWocketNote").value]);
	
	availWocketGrid.deleteRow(availWocketGrid.getSelectedRowId());//delete row from availabel wocket grid
	//clear all field
	document.getElementById("newWocketId").value = "";
	document.getElementById("newColorSet").value = "";
    document.getElementById("newHardwareVersion").value="";
    document.getElementById("newFirmwareVersion").value="";
    document.getElementById("newPrinted_Id").value = "";
    document.getElementById("newWocketNote").value = "";
	}
	else
		alert("Select wocket from wocket table to add.");
}

//removeWocketBtt onClick event remove wocket from selected list
function removeWocketFromList()
{
	var rowId = selectedWocketGrid.getSelectedRowId();
	if(rowId)
	{
	//create array from selected row
		var rowArray = [selectedWocketGrid.cellById(rowId,0).getTitle(),selectedWocketGrid.cellById(rowId,1).getTitle(),
	                	selectedWocketGrid.cellById(rowId,2).getTitle(),selectedWocketGrid.cellById(rowId,3).getTitle(),
	                	selectedWocketGrid.cellById(rowId,4).getTitle(),"Not Assigned",selectedWocketGrid.cellById(rowId,5).getTitle()];
		selectedWocketGrid.deleteRow(rowId);//delete row
		var nbrRows = availWocketGrid.getRowsNum();//get number of rows in wocket table
		availWocketGrid.addRow(nbrRows+1,rowArray);//add row into wocket table
	}
	else
		alert("Select wocket from selected list to remove.")

}

//newWocketsSubmit onclick event submit new selected wockets
function newWocketsSubmit()
{
	var selectedWocketIds = getSelectedWocketId();
	if(selectedWocketIds !="")
	{
		//get the ajax xmlHttp object from AjaxRequest.js included in layout.jsp page
		var xmlHttp = getAjaxGETRequest();
		var url = "assignNewWockets.html?wocketConcatStr="+selectedWocketIds;
		xmlHttp.onreadystatechange=function()
		{
			if (xmlHttp.readyState==4 && xmlHttp.status==200)
				{
					refreshGrid(assignedWocketGrid,availWocketGrid,"getPartAssignedWocket.html","getAvailableWocketList.html");
					selectedWocketGrid.clearAll();
				}
		}
		xmlHttp.open("GET",url,true);
		xmlHttp.send();
	}
	else
		alert("Please select wocket to assign.");
}

//return concat string of all selected wockets Id's seperated by '|' delimiter
function getSelectedWocketId()
{
	var nbrRows = selectedWocketGrid.getRowsNum();
	var concStrWocketID = "";
	for(var i=0; i<nbrRows;i++)
			concStrWocketID += selectedWocketGrid.cellByIndex(i,0).getTitle()+"|";

	return concStrWocketID;
}


//******change Div style to make visiable or hidden
function changeDivStyle(divId,displayStyle)
{	
	document.getElementById(divId).style.display = displayStyle;
}



</script>
</head>
<body onload="doOnLoad()">
<br/>
<!-- Personal Detail -->
<form:form name="personalInfoForm" action="updatePartPersonalInfo.html" method="GET" commandName="participant">
<h4>Personal Detail:</h4>

<label>Update Information:</label><input type="radio" name="personalSelect" value="yes" onclick="personalRadioButtYes()"/>Yes
<input type="radio" name="personalSelect" value="no" checked="checked" onclick="personalRadioButtNo()"/>No
<br/><br/>
<table>
<tr>
<td><label>Participant ID:</label></td><td><form:input path="participant_Id" name="pId" readonly="true" style="background-color: #D9D9D9;"/></td>
</tr>
<tr>
<td><label>First Name:</label></td><td><form:input path="fName" id="fName" name="fName"/></td>
<td><label>Last Name:</label></td><td><form:input path="lName" id="lName" name="lName"/></td>
</tr>

<tr>
<td><label>Gender:</label></td><td><form:input path="gender" id="gender" name="gender" readonly="true" size="1" style="background-color: #D9D9D9;"/>
<input type="radio" name="sex" value="M" id="sexM" onclick="sexRadionBttClick(this.value)"/>Male<input type="radio" name="sex" id="sexF" value="F" onclick="sexRadionBttClick(this.value)"/>Female</td>
</tr>

<tr>
<td><label>Birth Date:</label></td><td><form:input path="birth_Date" id="birthDate" name="birthDate" readonly="true" style="background-color: #D9D9D9;"/></td>
<td><label>Email:</label></td><td><form:input path="email" name="email" id="email"/></td>
</tr>

<tr>
<td><label>Height:</label></td><td><form:input path="height" name="height" id="height"/></td>
<td><label>Weight:</label></td><td><form:input path="weight" name="weight" id="weight"/></td>
</tr>

<tr>
<td><label>Race:</label></td><td><form:input path="race" name="race" id="race" readonly="true" style="background-color: #D9D9D9;"/></td>
<td colspan="2"><select name="race" id="raceCombo" onchange="setComboBoxValue(this.value,'race')">
<option value="">--Select--</option>
<option value="Hispanics">Hispanics</option>
<option value="Non-Hispanics">Non-Hispanics</option>
<option value="American Indian">American Indian</option>
<option value="Asian">Asian</option>
<option value="Hawaiian or Pacific Islander">Hawaiian or Pacific Islander</option>
<option value="Other">Other</option>
<option value="Two or More Races">Two or More Races</option>
</select></td>
</tr>

<tr>
<td><label>UTC Offset:</label></td><td><form:input path="utc_offset" name="utcOffset" id="utcOffset" readonly="true" style="background-color: #D9D9D9;"/></td>
<td colspan="2"><select name="utc_offsetCombo" id="utc_offsetCombo" onchange="setComboBoxValue(this.value,'utcOffset')">
<option value="">--Select--</option>
<option value="">Alabama UTC-05/6</option>
<option>Alaska UTC-09/10</option>
<option>American Samoa UTC-11</option>
<option>Arizona UTC-07</option>
</select></td>
</tr>

<tr>
<td><label>Comments:</label></td><td colspan="3"><form:textarea path="notes" rows="4" cols="30" id="personalNotes"/>
<form:hidden path="activeStatus"/>
</td>
</tr>
</table>
<br/>
<input type="button" value="Update Personal Info" id="personalSubmitBttn" onclick="updatePersonalInfoSubmit()" disabled="disabled" style="margin-left: 150px;"/>
</form:form>
<!-- Close Personal Detail -->
<br/>
<!-- --Phone-- -->
<h4>Phone Detail:</h4>
<label>Show Phone Detail:</label><input type="radio" name="phoneRadioBtt" value="yes" onclick="changeDivStyle('phoneDetail','')"/>Yes
<input type="radio" name="phoneRadioBtt" value="no" checked="checked" onclick="changeDivStyle('phoneDetail','none')"/>No<br/>
<br/>
<div id="phoneDetail" style="display: none;">
<label>Assigned Phone:</label><br/>
<div id="phoneGrid_Container" style="width:750px;height:100px;"></div>
<br/>
<label>Assign New Phone:</label><input type="radio" name="newPhoneRadioBttn" value="yes" onclick="changeDivStyle('assginNewPhone','')"/>Yes
<input type="radio" name="newPhoneRadioBttn" value="no" checked="checked" onclick="changeDivStyle('assginNewPhone','none')"/>No<br/>

<!-- Assign New Phone -->
<div id="assginNewPhone" style="display: none;">
<br/>
<label>Select Phone:</label><br/><br/>
<div id="avialPhGrid_Container" style="width:620px;height:100px;"></div>
<br/>
<label>Selected Phone:</label><br/>
<div id="newPhErrorDiv"></div>
<table>
<tr><td><label>IMEI:</label></td><td><input type="text" id="newPhIMEI" readonly="readonly" style="background-color:#D9D9D9;"></td>
</tr>
<tr>
<td><label>Phone Model:</label></td><td><input type="text" id="newPhModel" readonly="readonly" style="background-color:#D9D9D9;"></td> 
<td><label>Platform:</label></td><td><input type="text" id="newPhPlatform" readonly="readonly" style="background-color:#D9D9D9;"></td>
</tr>
<tr>
<td><label>OS Version</label></td><td><input type="text" id="newPhOSVersion" readonly="readonly" style="background-color:#D9D9D9;"></td>
<td><label>App Version</label></td><td><input type="text" id="newPhAppVersion" readonly="readonly" style="background-color:#D9D9D9;"></td>
</tr>
<tr>
<td><label>Reason:</label><label class="mandatory">*</label></td>
<td><select id="assignReason">
<option value="">--Select--</option>
<option value="Phone Break">Phone Break</option>
<option value="Phone Lost">Phone Lost</option>
<option value="Phone Technical Problem">Phone Technical Problem</option>
<option value="Other">Other</option>
<option value="N/A">N/A</option>
</select>
</td>
</tr>
</table>
<br/>

<input type="button" value="Assign Selected Phone" id="assgNewPhBttn" disabled="disabled" style="margin-left: 15em;" onclick="submitAssignNewPh()"/>

</div>
<!-- Assign New Phone close -->
<hr/>
<!-- Sim Deatil -->
<h4>Sim Card Detail:</h4>
<label>Show Sim Card Detail:</label><input type="radio" name="simRadioBtt" value="yes" onclick="changeDivStyle('simDetail','')"/>Yes
<input type="radio" name="simRadioBtt" value="no" checked="checked" onclick="changeDivStyle('simDetail','none')"/>No<br/>
<br/>
<div id="simDetail" style="display: none;">
<label>Assigned Sim Cards:</label><br/>
<div id="simGrid_Container" style="width:750px;height:100px;"></div>
<br/>
<label>Assign New Sim Card:</label><input type="radio" name="newSimRadioBttn" value="yes" onclick="changeDivStyle('assginNewSim','')"/>Yes
<input type="radio" name="newSimRadioBttn" value="no" checked="checked" onclick="changeDivStyle('assginNewSim','none')"/>No<br/>

<!-- Assign New Sim -->
<div id="assginNewSim" style="display: none;">
<br/>
<label>Select Sim Card:</label><br/><br/>
<div id="avialSimGrid_Container" style="width:650px;height:100px;"></div>
<br/>
<label>Selected Sim Card:</label><br/>
<div id="newSimErrorDiv"></div>
<table>
<tr>
<td><label>Phone Number:</label></td><td><input type="text" id="newSimPhoneNbr" maxlength="20" readonly="readonly" style="background-color:#D9D9D9;"></td>
<td><label>Carrier:</label></td><td><input type="text" id="newSimCarrier" readonly="readonly" style="background-color:#D9D9D9;"></td>
</tr>
<tr>
<td><label>Expiration Date:</label></td><td><input type="text" id="newSimcontExpDate"  readonly="readonly" style="background-color:#D9D9D9;"></td>
</tr>
<tr>
<td><label>Comments:</label></td><td colspan="2"><textarea rows="3" cols="30" id="newSimNote" readonly="readonly" style="background-color:#D9D9D9;"></textarea>
</tr>
<tr>
<td><label>Reason:</label><label class="mandatory">*</label></td>
<td><select id="assignSimReason">
<option value="">--Select--</option>
<option value="Phone Lost">Phone Lost</option>
<option value="Phone Technical Problem">Sim Technical Problem</option>
<option value="Other">Other</option>
<option value="N/A">N/A</option>
</select>
</td>
</tr>
</table>
<br/>
<input type="button" value="Assign Selected Sim card" id="assgNewSimBttn" disabled="disabled" style="margin-left: 15em;" onclick="submitAssignNewSim()"/>
</div><!-- Assign new Sim close -->
</div>
<!-- Sim Deatil Close -->
</div>

<!-- close phone -->
<hr/><hr/>
<!-- Wockets Detail -->
<h4>Wockets Detail:</h4>
<label>Show WocketS Detail:</label><input type="radio" name="wocketRadioBtt" value="yes" onclick="changeDivStyle('wocketDetail','')"/>Yes
<input type="radio" name="wocketRadioBtt" value="no" checked="checked" onclick="changeDivStyle('wocketDetail','none')"/>No<br/>
<br/>
<div id="wocketDetail" style="display: none;"><!-- Wocket detail grid -->
<label>Assigned Wockets:</label><br/>
<div id="wocketGrid_Container" style="width:700px;height:100px;"></div>
<br/>
<label>Assign New Wockets:</label><input type="radio" name="newWocketRadioBtt" value="yes" onclick="changeDivStyle('assignNewWocketDiv','')"/>Yes
<input type="radio" name="newWocketRadioBtt" value="no" checked="checked" onclick="changeDivStyle('assignNewWocketDiv','none')"/>No<br/>
<div id="assignNewWocketDiv" style="display: none;">

<h4>Available Wockets:</h4>
<div id="availWocketgrid_container" style="width:750px;height:150px;"></div>

<h4>Selected Wocket:</h4>
<div id="wocketErrorDiv"></div>
<table>
<tr>
<td><label>Wocket Id:</label></td><td><input type="text" name="wocketId" id="newWocketId" readonly="readonly" style="background-color: #D9D9D9;"/></td>
</tr>
<tr>
<td><label>Color Set:</label></td><td><input type="text" name="colorSet" id="newColorSet" readonly="readonly" style="background-color: #D9D9D9;"/></td>
<td><label>Hardware Version:</label></td><td><input type="text" name="hardwareVersion" readonly="readonly" id="newHardwareVersion" style="background-color: #D9D9D9;"/></td>
</tr>
<tr>
<td><label>Firmware Version:</label></td><td><input type="text" name="firmwareVersion" readonly="readonly" id="newFirmwareVersion" style="background-color: #D9D9D9;"/></td>
<td><label>Printed Id:</label></td><td><input type="text" name="printed_Id" id="newPrinted_Id" readonly="readonly" style="background-color: #D9D9D9;"/></td>
</tr>
<tr>
<td><label>Notes:</label></td><td colspan="2"><textarea rows="3" cols="30" name="wocketNote" id="newWocketNote" readonly="readonly" style="background-color: #D9D9D9;"></textarea>
<td><input type="button" value="Add to List" id="addWocketToList" disabled="disabled" onclick="addWocketToList();"/></td>
</tr>
</table>
<!-- wocket grid close -->


<!-- selected wocket Div -->
<h4>Selected Wockets List</h4>
<div id="selectedWocketGrid_container" style="width:700px;height:120px;"></div>
<input type="button" value="Remove Wocket" id="removeWocketBtt" onclick="removeWocketFromList();"/>
<br/><br/>
<input type="button" id="newWocketsSubmit" value="  Assign Selected Wockets  " style="margin-left: 150px;" onclick="newWocketsSubmit()"/>

<!-- selected wocket close -->

</div>

</div><!-- wocket detail grid close -->

</body>
</html>