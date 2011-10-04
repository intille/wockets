<%@ page language="java" contentType="text/html; charset=ISO-8859-1"
    pageEncoding="ISO-8859-1"%>
    <%@taglib uri="http://www.springframework.org/tags/form" prefix="form"%>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=ISO-8859-1">
<title>Wockets - New Participant</title>
	<link rel="stylesheet" type="text/css" href="dhtmlx/dhtmlxCalendar/codebase/dhtmlxcalendar.css"></link>
	<link rel="stylesheet" type="text/css" href="dhtmlx/dhtmlxCalendar/codebase/skins/dhtmlxcalendar_dhx_skyblue.css"></link>
	<script src="dhtmlx/dhtmlxCalendar/codebase/dhtmlxcalendar.js"></script>
<style type="text/css">
.mandatory{
color:#ff0000;
}
</style>

<script>
	var phoneGrid;
	var simGrid;
	var wocketGrid;
	var studyGrid;
	var selectedWocketGrid;
	var selectedStudyGrid;
	function doOnLoad() {
	//Available phone grid init
		phoneGrid = new dhtmlXGridObject('avilPhone_Container');//create grid object
		phoneGrid.setImagePath("dhtmlx/imgs/");
		phoneGrid.setHeader("IMEI,Phone Model,Platform,OS Version,App Version,Is Assigned");
		phoneGrid.setInitWidths("120,120,120,120,120,*");
		phoneGrid.setColAlign("left,left,left,left,left,left");
		phoneGrid.setSkin("light");
		phoneGrid.setColSorting("str,str,str,str,str,str");
		phoneGrid.setColTypes("ro,ro,ro,ro,ro,ro");
		phoneGrid.init();
		phoneGrid.attachEvent("onRowSelect",phoneGridRowSelected);
		phoneGrid.load("getAvailPhoneDirectory.html","json");//load phones
		
	//Available simcard gird init	
		simGrid = new dhtmlXGridObject('simgrid_container');
		simGrid.setImagePath("dhtmlx/imgs/");
		simGrid.setHeader("Phone Number,Carrier,Expiration Date,Is Assigned,Notes");
		simGrid.setInitWidths("120,120,120,120,*");
		simGrid.setColAlign("left,left,left,left,left,left");
		simGrid.setSkin("light");
		simGrid.setColSorting("str,str,date,str,str,str");
		simGrid.setColTypes("ro,ro,ro,ro,ro,ro");
		simGrid.init();
		simGrid.attachEvent("onRowSelect",simGridRowSelected);
		simGrid.load("getAvailableSimcardList.html","json");//load simcards
		
	//Available wocket grid init
		wocketGrid = new dhtmlXGridObject('wocketgrid_container');
		wocketGrid.setImagePath("dhtmlx/imgs/");
		wocketGrid.setHeader("Wocket Id,Color Set,Hardware Version,Firmware Version,Printed Id,Is Assigned,Notes");
		wocketGrid.setInitWidths("120,120,120,120,120,120,*");
		wocketGrid.setColAlign("left,left,left,left,left,left,left");
		wocketGrid.setSkin("light");
		wocketGrid.setColSorting("str,str,str,str,str,str,str");
		wocketGrid.setColTypes("ro,ro,ro,ro,ro,ro,ro");
		wocketGrid.init();
	    wocketGrid.attachEvent("onRowSelect",wocketGridRowSelected);
		wocketGrid.load("getAvailableWocketList.html","json");//load simcards
	
	//Study List	
    	studyGrid = new dhtmlXGridObject('studyGrid_Container');
    	studyGrid.setImagePath("dhtmlx/imgs/");
    	studyGrid.setHeader("Study Id,Description");
    	studyGrid.setInitWidths("100,*");
    	studyGrid.setColAlign("left,left");
    	studyGrid.setSkin("light");
    	studyGrid.setColSorting("str,str");
    	studyGrid.setColTypes("ro,ro");
    	studyGrid.init();
    	studyGrid.attachEvent("onRowSelect",studyGridRowSelected);
    	studyGrid.load("getStudyList.html","json");
	
	//init dhtmlx calendar
    	var calendar = new dhtmlXCalendarObject(["startDate","endDate","birthDate"]);//attached calander object to text fields startDate and endDate
    	calendar.hideTime();
    	var currentDate = calendar.getDate("%Y.%m.%d");
    	var y = calendar.getFormatedDate("%Y", currentDate);
    	var m = calendar.getFormatedDate("%m", currentDate);
       	var d = calendar.getFormatedDate("%d", currentDate);
    	//document.getElementById("startDate").value = currentDate;
    	calendar.setInsensitiveRange(null,y+"-"+m+"-"+(d-1));//disable date before current date
    	var calendarBDate = new dhtmlXCalendarObject(["birthDate"]);//attached calander object to text birthdate
    	calendarBDate.hideTime();
    	
	
    //init selected wocket list grid
    	selectedWocketGrid = new dhtmlXGridObject('selectedWocketGrid_container');
    	selectedWocketGrid.setImagePath("dhtmlx/imgs/");
    	selectedWocketGrid.setHeader("Wocket Id,Color Set,Hardware Version,Firmware Version,Printed Id,Notes");
    	selectedWocketGrid.setInitWidths("120,120,120,120,120,*");
    	selectedWocketGrid.setColAlign("left,left,left,left,left,left");
    	selectedWocketGrid.setSkin("light");
    	selectedWocketGrid.setColSorting("str,str,str,str,str,str");
    	selectedWocketGrid.setColTypes("ro,ro,ro,ro,ro,ro");
    	selectedWocketGrid.init();
	
    //init selected study grid
    	selectedStudyGrid = new dhtmlXGridObject('selectedStudyGrid_container');
    	selectedStudyGrid.setImagePath("dhtmlx/imgs/");
    	selectedStudyGrid.setHeader("Study Id,Start Time,End Time,Description");
    	selectedStudyGrid.setInitWidths("100,100,100,*");
    	selectedStudyGrid.setColAlign("left,left,left,left");
    	selectedStudyGrid.setSkin("light");
    	selectedStudyGrid.setColSorting("str,str,str,str");
    	selectedStudyGrid.setColTypes("ro,ro,ro,ro");
    	selectedStudyGrid.init();

 }
	
	//phone grid onClick event
	function phoneGridRowSelected(rowID)
    {
    	document.getElementById("IMEI").value = phoneGrid.cellById(rowID,0).getTitle();
    	document.getElementById("phoneModel").value = phoneGrid.cellById(rowID,1).getTitle();
    	document.getElementById("platform").value = phoneGrid.cellById(rowID,2).getTitle();
    	document.getElementById("OSVersion").value = phoneGrid.cellById(rowID,3).getTitle();
    	document.getElementById("appVersion").value = phoneGrid.cellById(rowID,4).getTitle(); 
    }
	
	//sim grid onClick event
	function simGridRowSelected(rowID)
    {
    	document.getElementById("phoneNbr").value = simGrid.cellById(rowID,0).getTitle();
    	document.getElementById("carrier").value = simGrid.cellById(rowID,1).getTitle();
    	document.getElementById("expDate").value = simGrid.cellById(rowID,2).getTitle();
    	document.getElementById("simNotes").value = simGrid.cellById(rowID,4).getTitle();
    }
	
	//wocket grid onClick event
	function wocketGridRowSelected(rowID)
    {
    	document.getElementById("wocketId").value = wocketGrid.cellById(rowID,0).getTitle();
    	document.getElementById("colorSet").value = wocketGrid.cellById(rowID,1).getTitle();
    	document.getElementById("hardwareVersion").value = wocketGrid.cellById(rowID,2).getTitle();
    	document.getElementById("firmwareVersion").value = wocketGrid.cellById(rowID,3).getTitle();
    	document.getElementById("printed_Id").value = wocketGrid.cellById(rowID,4).getTitle();
    	document.getElementById("wocketNote").value = wocketGrid.cellById(rowID,6).getTitle();
    }
	
	//Study grid onClick event	
	function studyGridRowSelected(rowID)
    {
    	document.getElementById("studyId").value = studyGrid.cellById(rowID,0).getValue();
    	document.getElementById("desc").value = studyGrid.cellById(rowID,1).getValue();
    	document.getElementById("addStudyBttn").disabled = false;
    	document.getElementById("endDate").value="";
    	document.getElementById("startDate").value="";
     }


//radio button click event	
function radioBttClick(divId,radioValue)
{
	if(radioValue == 'yes')
		document.getElementById(divId).style.display = '';
	else
		document.getElementById(divId).style.display = 'none';
}

//create error label
function createErrorLabel(message,parent,id)
{
	var errorLabel = document.getElementById(id);
	if(errorLabel)
		parent.removeChild(document.getElementById(id));
	var errorLabel = document.createElement('label');
	errorLabel.setAttribute('id',id);
	errorLabel.innerHTML= message;
	errorLabel.style.color = 'red';
	parent.appendChild(errorLabel);
}

//get radio button value
function checkRadioButton(radioButtonName)
{	
	var radioValue="";
	var radioButtons = document.getElementsByName(radioButtonName);
	for (i=0; i<radioButtons.length; i++)
	{
		  if (radioButtons[i].checked == true)
			  radioValue = radioButtons[i].value;
  	}
	return radioValue;
}

//submit Form
function submitForm()
{
	var enrollStudy = checkRadioButton("enrollRadio");
	
	if(	document.getElementById("fName").value==""||
		document.getElementById("lName").value==""||
		document.getElementById("email").value==""||
		document.getElementById("utc_offset").value =="")
		createErrorLabel("All * mark field are mandatory",document.getElementById("personalDetErrorDiv"),'persErrorLabel');
	
	else if(enrollStudy == 'yes')
		{
			if(validateStudy()|| validatePhone() || validateSim() || validateWocket())
				alert("Please select all required fields.");
			else
				{
					document.getElementById("wocketConcatStr").value = getSelectedWocketId();
					document.getElementById("concatStudyStr").value = getSelectedStudyConcatStr();
					document.participantForm.submit();
				}
		}
	else
		{
			document.getElementById("wocketConcatStr").value = getSelectedWocketId();//reset value to ""
			document.getElementById("concatStudyStr").value = getSelectedStudyConcatStr();//reset value to ""
			document.participantForm.submit();
		}

}

//validate study selecttion
function validateStudy()
{
	var errorStatus = false;
	var studyErrorMessg = "";
	if(document.getElementById("studyId").value =="" || document.getElementById("desc").value == "")
		{
		studyErrorMessg += "Please select study from table.<br/>";
		errorStatus = true;
		}
	if(document.getElementById("startDate").value == "" || document.getElementById("endDate").value == "")
		{
		studyErrorMessg += "Please select start and end date.";
		errorStatus = true;
		}
	createErrorLabel(studyErrorMessg, document.getElementById("studyErrorDiv"),'studyErrorLabel');
	return errorStatus;

}

//validate phone selection
function validatePhone()
{
	var errorStatus = false;
	if(document.getElementById("IMEI").value == "")
		{
			createErrorLabel("Please select phone from phone table",document.getElementById("phoneErrorDiv"),'phoneErrorLabel');
			errorStatus = true;
		}
	return errorStatus;
}

//validate sim selection
function validateSim()
{
	var errorStatus = false;
	if(document.getElementById("phoneNbr").value == "")
		{
			createErrorLabel("Please select Sim card from Sim cards table",document.getElementById("simErrorDiv"),'simErrorLabel');
			errorStatus = true;
		}
	return errorStatus;
}

//validate wocket selection
function validateWocket()
{
	var errorStatus = false;
	//if(document.getElementById("wocketId").value == "")
	if(selectedWocketGrid.getRowsNum()<1)
		{
			createErrorLabel("Please select wocket from wockets table",document.getElementById("wocketErrorDiv"),'wocketErrorLabel');
			errorStatus = true;
		}
	return errorStatus;
}

//add wocket to selected List
function addWocketToList()
{
	if(wocketGrid.getSelectedRowId())
	{
	var nbrRows = selectedWocketGrid.getRowsNum();
	selectedWocketGrid.addRow(nbrRows+1,[document.getElementById("wocketId").value,document.getElementById("colorSet").value,
	                                     document.getElementById("hardwareVersion").value,document.getElementById("firmwareVersion").value,
	                                     document.getElementById("printed_Id").value,document.getElementById("wocketNote").value]);
	
	wocketGrid.deleteRow(wocketGrid.getSelectedRowId());
	//wocketGrid.clearSelection();
	document.getElementById("wocketId").value = "";
	document.getElementById("colorSet").value = "";
    document.getElementById("hardwareVersion").value="";
    document.getElementById("firmwareVersion").value="";
    document.getElementById("printed_Id").value = "";
    document.getElementById("wocketNote").value = "";
	}
	else
		alert("Select wocket from wocket table to add.");

}

//remove wocket from selected list
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
		var nbrRows = wocketGrid.getRowsNum();//get number of rows in wocket table
		wocketGrid.addRow(nbrRows+1,rowArray);//add row into wocket table
	}
	else
		alert("Select wocket from selected list to remove.")

}

//addStudyBttn button onClick event
function addStudyToList()
{	
	//validate study already exist or not in selected list
	var selectedStudyId = document.getElementById("studyId").value;
	for(var i=0; i < selectedStudyGrid.getRowsNum(); i++){
		if(selectedStudyGrid.cellByIndex(i, 0).getTitle() == selectedStudyId){
			createErrorLabel("Study already added to list.", document.getElementById("studyErrorDiv"),'studyExistErrorLabel');
			return;
		}
	}
	createErrorLabel("", document.getElementById("studyErrorDiv"),'studyExistErrorLabel');
	if(validateStudy()==false)
		{
			var studyArray = [selectedStudyId,document.getElementById("startDate").value,
			                  document.getElementById("endDate").value,document.getElementById("desc").value];  //Array to insert into selected study grid
			selectedStudyGrid.addRow(selectedStudyGrid.getRowsNum()+1,studyArray);
		}
}

//removeStudyBttn button onClick event
function removeStudyFromList()
{
	selectedStudyGrid.deleteSelectedRows();
}

//return the selected wocket Id concat String seperated by '|' character
function getSelectedWocketId()
{
	var nbrRows = selectedWocketGrid.getRowsNum();
	var concStrWocketID = "";
	for(var i=0; i<nbrRows;i++)
			concStrWocketID += selectedWocketGrid.cellByIndex(i,0).getTitle()+"|";

	return concStrWocketID;
}

/*****return selected study details concat string seperated by '|' delimiter  
and each record has formate studyId:startDate:endDate|studyId:startDate:endDate|....*****/
function getSelectedStudyConcatStr()
{
	var nbrRows = selectedStudyGrid.getRowsNum();
	var concStrWocketID = "";
	for(var i=0; i<nbrRows;i++)
			concStrWocketID +=  selectedStudyGrid.cellByIndex(i,0).getTitle()+":"+//study Id
								selectedStudyGrid.cellByIndex(i,1).getTitle()+":"+//start date
								selectedStudyGrid.cellByIndex(i,2).getTitle()+"|";//end date
	return concStrWocketID;
}

	
</script>
</head>
<body onload="doOnLoad();">
<h3>Register New Participant</h3>
<br/>
<h4>Personal Detail:</h4>
<div id="personalDetErrorDiv"></div>
<form:form action="registerNewParticipant.html" method="post" commandName="participant" name="participantForm">
<table>
<tr>
<td><label>First Name:</label><label class="mandatory">*</label></td><td><form:input path="fName" id="fName"/></td>
<td><label>Last Name:</label><label class="mandatory">*</label></td><td><form:input path="lName" id="lName"/></td>
</tr>
<tr>
<td><label>Gender:</label></td>
<td><form:radiobutton path="gender" value="M"/>Male<form:radiobutton path="gender" value="F"/>Female</td>
</tr>
<tr><td><label>Birth Date:</label></td><td><form:input path="birth_Date" id="birthDate" readonly="true" style="background-color: #D9D9D9;"/></td>
</tr>
<tr><td><label>Email:</label><label class="mandatory">*</label></td><td><form:input path="email" id="email"/></td>
</tr>
<tr><td><label>Height:</label></td><td><form:input path="height" maxlength="6"/></td>
<td><label>Weight:</label></td><td><form:input path="weight" maxlength="6"/></td>
</tr>
<tr><td><label>Race:</label></td>
<td>
<form:select path="race">
<form:option value="">--Select--</form:option>
<form:option value="Hispanics">Hispanics</form:option>
<form:option value="Non-Hispanics">Non-Hispanics</form:option>
<form:option value="American Indian">American Indian</form:option>
<form:option value="Asian">Asian</form:option>
<form:option value="Hawaiian or Pacific Islander">Hawaiian or Pacific Islander</form:option>
<form:option value="Other">Other</form:option>
<form:option value="Two or More Races">Two or More Races</form:option>
</form:select>
</td>
</tr>
<tr>
<td><label>Time zone:</label><label class="mandatory">*</label></td>
<td>
<form:select path="utc_offset" id="utc_offset">
<form:option value="">--Select--</form:option>
<form:option value="6">Alabama UTC-05/6</form:option>
<option>Alaska UTC-09/10</option>
<option>American Samoa UTC-11</option>
<option>Arizona UTC-07</option>
</form:select>
</td>
</tr>
<tr>
<td><label>Comments:</label></td>
<td colspan="3"><form:textarea path="notes" cols="35" rows="6" id="notes"></form:textarea></td>
</tr>
</table>

<hr/><hr/>
<!-- Enroll in a Study -->
<table>
<tr><td><h4>Enroll in Study:</h4></td><td><input type="radio" name="enrollRadio" value="yes" onclick="radioBttClick('enrollStudy',this.value);">Yes
<input type="radio" name="enrollRadio" value="no" checked="checked" onclick="radioBttClick('enrollStudy',this.value);">No
</tr>
</table>
<div id="enrollStudy" style="display: none;">
<h4>Study List:</h4>
<div id="studyGrid_Container" style="width:400px;height:150px;"></div>
<h4>Selected Study:</h4>
<div id="studyErrorDiv"></div>
<table>
<tr><td><label>Study Id:</label><label class="mandatory">*</label></td><td><input type="text" name="studyId" id="studyId" readonly="readonly" style="background-color: #D9D9D9;"/></td>
<td><label>Description:</label><label class="mandatory">*</label></td><td><input type="text" name="desc" id="desc" readonly="readonly" style="background-color: #D9D9D9;"/></td>
</tr>
<tr>
<td><label>Start Date:</label><label class="mandatory">*</label></td><td><input type="text" id="startDate" name="startDate" readonly="readonly" style="background-color: #D9D9D9;"/></td>
<td><label>End Date:</label><label class="mandatory">*</label></td><td><input type="text" id="endDate" name="endDate" readonly="readonly" style="background-color: #D9D9D9;"/></td>
<td><input type="button" id="addStudyBttn" value="Add to List" disabled="disabled" onclick="addStudyToList();"/></td>
</tr> 
</table>

<!-- selected Study Div -->
<h4>Selected Study List</h4>
<div id="selectedStudyGrid_container" style="width:600px;height:120px;"></div>
<input type="hidden" id="concatStudyStr" name="concatStudyStr"/>
<input type="button" value="Remove Study" id="removeStudyBttn" onclick="removeStudyFromList();"/>
<!-- selected Study close -->

<hr/>
<table>
<tr><td><label>Assign Phone:</label></td><td>&nbsp;&nbsp;&nbsp;&nbsp;<input type="radio" name="phoneRadio" value="yes" onclick="radioBttClick('assignPhone',this.value);">Yes
<input type="radio" name="phoneRadio" value="no" checked="checked" onclick="radioBttClick('assignPhone',this.value);">No
</tr>
</table>
<!-- Phone grid -->
<div id="assignPhone"  style="display: none;">
<h4>Available Phone:</h4>
<div id="avilPhone_Container" style="width:720px;height:150px;"></div>
<h4>Selected Phone:</h4>
<div id="phoneErrorDiv"></div>
<table>
<tr>
<td><label>IMEI:</label><label class="mandatory">*</label></td><td><input type="text" id="IMEI" name="IMEI" readonly="readonly" style="background-color: #D9D9D9;"/></td>
</tr>
<tr>
<td><label>Phone Model:</label><label class="mandatory">*</label></td><td><input type="text" name="phoneModel" id="phoneModel" readonly="readonly" style="background-color: #D9D9D9;"/></td>
<td><label>Platform:</label><label class="mandatory">*</label></td><td><input type="text" name="platform" id="platform" readonly="readonly" style="background-color: #D9D9D9;"/></td>
</tr>
<tr>
<td><label>OS Version:</label><label class="mandatory">*</label></td><td><input type="text" name="OSVersion" id="OSVersion" readonly="readonly" style="background-color: #D9D9D9;"/></td>
<td><label>App Version:</label><label class="mandatory">*</label></td><td><input type="text" name="appVersion" id="appVersion" readonly="readonly" style="background-color: #D9D9D9;"/></td>
</tr>
</table>
<hr/>
</div>


<table>
<tr><td><label>Assign Simcard:</label></td><td>&nbsp;<input type="radio" name="simRadio" value="yes" onclick="radioBttClick('assignSimcard',this.value);">Yes
<input type="radio" name="simRadio" value="no" checked="checked" onclick="radioBttClick('assignSimcard',this.value);">No
</tr>
</table>
<!-- Sim Grid -->
<div id="assignSimcard" style="display: none;">
<h4>Available Simcards:</h4>
<div id="simgrid_container" style="width:750px;height:150px;"></div>
<h4>Selected Simcard:</h4>
<div id="simErrorDiv"></div>
<table>
<tr>
<td><label>Phone Number:</label></td><td><input type="text" name="phoneNbr" id="phoneNbr" readonly="readonly" style="background-color: #D9D9D9;"/></td>
</tr>
<tr>
<td><label>Carrier:</label></td><td><input type="text" name="carrier" id="carrier" readonly="readonly" style="background-color: #D9D9D9;"/></td>
<td><label>Expiration Date:</label></td><td><input type="text" name="expDate" id="expDate" readonly="readonly" style="background-color: #D9D9D9;"/></td>
</tr>
<tr>
<td><label>Comments:</label></td><td colspan="3"><textarea rows="6" cols="30" name="simNotes" id="simNotes" readonly="readonly" style="background-color: #D9D9D9;"></textarea></td>
</tr>
</table>
<hr/>
</div>


<table>
<tr><td><label>Assign Wockets:</label></td><td><input type="radio" name="wocketRadio" value="yes" onclick="radioBttClick('assignWocket',this.value);">Yes
<input type="radio" name="wocketRadio" value="no" checked="checked" onclick="radioBttClick('assignWocket',this.value);">No
</tr>
</table>
<!-- Wockets Grid -->
<div id="assignWocket" style="display: none;">
<h4>Available Wockets:</h4>
<div id="wocketgrid_container" style="width:850px;height:150px;"></div>


<!-- wocket grid -->
<h4>Selected Wocket:</h4>
<div id="wocketErrorDiv"></div>
<table>
<tr>
<td><label>Wocket Id:</label></td><td><input type="text" name="wocketId" id="wocketId" readonly="readonly" style="background-color: #D9D9D9;"/></td>
</tr>
<tr>
<td><label>Color Set:</label></td><td><input type="text" name="colorSet" id="colorSet" readonly="readonly" style="background-color: #D9D9D9;"/></td>
<td><label>Hardware Version:</label></td><td><input type="text" name="hardwareVersion" readonly="readonly" id="hardwareVersion" style="background-color: #D9D9D9;"/></td>
</tr>
<tr>
<td><label>Firmware Version:</label></td><td><input type="text" name="firmwareVersion" readonly="readonly" id="firmwareVersion" style="background-color: #D9D9D9;"/></td>
<td><label>Printed Id:</label></td><td><input type="text" name="printed_Id" id="printed_Id" readonly="readonly" style="background-color: #D9D9D9;"/></td>
</tr>
<tr>
<td><label>Notes:</label></td><td colspan="2"><textarea rows="3" cols="30" name="wocketNote" id="wocketNote" readonly="readonly" style="background-color: #D9D9D9;"></textarea>
<td><input type="button" value="Add to List" onclick="addWocketToList();"/></td>
</tr>
</table>
<!-- wocket grid close -->


<!-- selected wocket Div -->
<h4>Selected Wockets List</h4>
<div id="selectedWocketGrid_container" style="width:750px;height:120px;"></div>
<input type="hidden" name="wocketConcatStr" id="wocketConcatStr"/>
<input type="button" value="Remove Wocket" id="removeWocketBtt" onclick="removeWocketFromList();"/>
<!-- selected wocket close -->

</div>


</div><!-- Enroll study Div close -->


<hr/>
<br/>
<input type="button" value="   Add Participant   " onclick="submitForm();"/>




</form:form>
</body>
</html>