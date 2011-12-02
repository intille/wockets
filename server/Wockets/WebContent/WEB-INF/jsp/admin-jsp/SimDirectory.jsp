<%@ page language="java" contentType="text/html; charset=ISO-8859-1"
    pageEncoding="ISO-8859-1"%>
    <%@taglib uri="http://www.springframework.org/tags/form" prefix="form"%>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=ISO-8859-1">
<title>Wockets - SimCard Directory</title>
<link rel="stylesheet" type="text/css" href="dhtmlx/dhtmlxCalendar/codebase/dhtmlxcalendar.css"></link>
	<link rel="stylesheet" type="text/css" href="dhtmlx/dhtmlxCalendar/codebase/skins/dhtmlxcalendar_dhx_skyblue.css"></link>
	<script src="dhtmlx/dhtmlxCalendar/codebase/dhtmlxcalendar.js"></script>
<script type="text/javascript">
var mygrid;
function doInitGrid(){
	mygrid = new dhtmlXGridObject('simgrid_container');
    mygrid.setImagePath("dhtmlx/imgs/");
    mygrid.setHeader("Phone Number,Carrier,Expiration Date,Is Assigned,Notes");
    mygrid.setInitWidths("120,120,120,120,*");
    mygrid.setColAlign("left,left,left,left,left,left");
    mygrid.setSkin("light");
    mygrid.setColSorting("str,str,date,str,str,str");
    mygrid.setColTypes("ro,ro,ro,ro,ro,ro");
    mygrid.init();
    mygrid.attachEvent("onRowSelect",doOnRowSelected);
	mygrid.load("getSimcardList.html","json");
	makeAllFieldEditable();
	
	//init dhtmlx calander
	var calendar = new dhtmlXCalendarObject(["contractExpDate"]);//attached calander object to text fields birthDate
	calendar.hideTime();
	document.getElementById("contractExpDate").style.background= "#D9D9D9";
}

function doOnRowSelected(rowID)
{
	var phoneNbr = mygrid.cellById(rowID,0);
	var carrier = mygrid.cellById(rowID,1);
	var expDate = mygrid.cellById(rowID,2);
	var isAssigned = mygrid.cellById(rowID,3);
	var notes = mygrid.cellById(rowID,4);
	
	document.getElementById("phoneNbr").value = phoneNbr.getValue();
	document.getElementById("carrier").value = carrier.getValue().replace("&amp;","&"); //replace &amp with & if exist
	document.getElementById("contractExpDate").value = expDate.getValue();
	document.getElementById("notes").value = notes.getValue();
	var assignedValue = isAssigned.getValue();
	if(assignedValue=='Assigned')
	{
		document.getElementById("isAssigned").value = "1";
		document.getElementById("delete").disabled = true; 
	}
	else
	{
		document.getElementById("isAssigned").value = "0";
		document.getElementById("delete").disabled = false;
	}
   	//reset radio button
   	resetRadioButton();
   	makeAllFieldReadOnly();
}

function resetRadioButton()
{
   	for (var i=0; i<document.getElementsByName("select").length; i++)
		document.getElementsByName("select")[i].checked = false;
}

function radioButtonClick(radioValue)
{
	
	document.getElementById("action").value = radioValue;//set radio button value to hidden field
	//1 for add 2 for update and 3 for delete	
	switch(radioValue)
		{
		case '1':
            makeAllFieldEditable();
	    	mygrid.clearSelection();
			break;
		case '2':
			if(!mygrid.getSelectedRowId())
				alert("Please select simcard from simcard table for update.");
			else{
	    	document.getElementById("phoneNbr").readOnly = true;
	    	document.getElementById("carrier").readOnly = true;
	    	document.getElementById("phoneNbr").style.background= "#D9D9D9";
	    	document.getElementById("carrier").style.background= "#D9D9D9";
	    	document.getElementById("notes").readOnly = false;
	    	document.getElementById("notes").style.background= "#FCFCFC";
	  			}
			break;
		case '3':
			if(!mygrid.getSelectedRowId())
				alert("Please select study from study table for delete.");
			else
			{
				makeAllFieldReadOnly();
				doOnRowSelected(mygrid.getSelectedRowId());
				document.getElementsByName("select")[2].checked = true;
			}
		}
}


function makeAllFieldReadOnly()
{
	//make read only
	document.getElementById("phoneNbr").readOnly = true; 
	document.getElementById("carrier").readOnly = true;
	document.getElementById("notes").readOnly = true;
	//change color
	document.getElementById("phoneNbr").style.background= "#D9D9D9";
	document.getElementById("carrier").style.background= "#D9D9D9";
	document.getElementById("notes").style.background= "#D9D9D9";
}

function makeAllFieldEditable()
{
	//clear all value
	document.getElementById("phoneNbr").value = ""; 
	document.getElementById("carrier").value = "";
	document.getElementById("notes").value = "";
	document.getElementById("isAssigned").value = "0";
	document.getElementById("contractExpDate").value = "";
	//make read only false
	document.getElementById("phoneNbr").readOnly = false; 
	document.getElementById("carrier").readOnly = false;
	document.getElementById("notes").readOnly = false;
	//change color
	document.getElementById("phoneNbr").style.background= "#FCFCFC";
	document.getElementById("carrier").style.background= "#FCFCFC";
	document.getElementById("notes").style.background= "#FCFCFC";
	
	document.getElementById("delete").disabled = false;
}

function createErrorLabel(message,parent)
{
	var errorLabel = document.createElement('label');
	errorLabel.setAttribute('id',"errorLabel");
	errorLabel.innerHTML= message;
	errorLabel.style.color = 'red';
	parent.appendChild(errorLabel);
}

function refreshGrid()
{
	mygrid.selectAll();
	mygrid.deleteSelectedItem();
	mygrid.load("getSimcardList.html","json");
}

function checkRadioButton()
{
	var radioButtons = document.getElementsByName("select");
	var radioValue="";
	for (i=0; i<radioButtons.length; i++)
	{
		if (radioButtons[i].checked == true)
				radioValue = radioButtons[i].value;
  	}
	return radioValue;
}


function submitSimcard()
{	

	var errorDiv = document.getElementById("errorDiv");
   	var label = document.getElementById("errorLabel");
	if(label)
		errorDiv.removeChild(label);

	var radioValue=checkRadioButton();
	
   	//reset radio button
   	resetRadioButton();
	
	if(document.getElementById("phoneNbr").value==""||
		document.getElementById("carrier").value == ""||
		document.getElementById("contractExpDate").value == "")
			createErrorLabel("All fields are mendatory.",errorDiv);
   	else if(radioValue=="")
   		createErrorLabel("Select type of action before submit.",errorDiv);
   		
	else
		document.simCardForm.submit(); 
}




</script>

</head>
<body onload="doInitGrid();">
<h3>Simcard Directory</h3>

<div id="simgrid_container" style="width:750px;height:200px;"></div>

<h4>Manage Simcard</h4>
<form:form name="simCardForm" action="submitSimcard.html" method="GET" commandName="sim">
<div id="errorDiv"></div>
<table>
<tr><td>Select:</td>
<td><input type="radio" id="add" name="select" value="1" onclick="radioButtonClick(this.value);" checked="checked"/>Add
<input type="radio" id="update" name="select" value="2" onclick="radioButtonClick(this.value);"/>Update
<input type="radio" id="delete" name="select" value="3" onclick="radioButtonClick(this.value);"/>Delete</td>
</tr>
<tr>
<td><label>Phone Number:</label></td><td><form:input path="phoneNbr" id="phoneNbr" maxlength="20"/></td>
<td><label>Carrier:</label></td><td><form:input path="carrier" id="carrier"/></td>
</tr>
<tr>
<td><label>Expiration Date:</label></td><td><form:input path="contractExpDate" id="contractExpDate"  readonly="true"/>
<form:hidden path="isAssigned" id="isAssigned" value="0"/>
</td>
</tr>
<tr>
<td><label>Comments:</label></td><td><form:textarea path="notes" cols="28" rows="6" id="notes"/>
</tr>
<tr><td></td><td>
<input type="hidden" name="action" id="action" value="1"/>
<input type="button" value="Submit" onclick="submitSimcard();"/></td></tr>
</table>
</form:form>
<br/><br/><br/><br/><br/><br/><br/><br/><br/>
</body>
</html>