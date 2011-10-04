<%@ page language="java" contentType="text/html; charset=ISO-8859-1"
    pageEncoding="ISO-8859-1"%>
    <%@taglib uri="http://www.springframework.org/tags/form" prefix="form"%>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=ISO-8859-1">
<title>Wockets - Wockets Directory</title>

<script type="text/javascript">
 var mygrid;
    function doInitGrid(){
    	mygrid = new dhtmlXGridObject('Wocketsgrid_container');//create grid object
        mygrid.setImagePath("dhtmlx/imgs/");
        mygrid.setHeader("Wockets Id,Color Set,Hardware Version,Firmware Version,Printed Id,Is Assigned,Notes");
        mygrid.setInitWidths("120,120,120,120,120,120,*");
        mygrid.setColAlign("left,left,left,left,left,left,left");
        mygrid.setSkin("light");
        mygrid.setColSorting("str,str,str,str,str,str,str");
        mygrid.setColTypes("ro,ro,ro,ro,ro,ro,ro");
        mygrid.init();
        mygrid.attachEvent("onRowSelect",doOnRowSelected);
        mygrid.load("getWocketseDirectory.html","json");
        clearAllTextField();
   }
    function doOnRowSelected(rowID)
    {
    	document.getElementById("wocketId").value = mygrid.cellById(rowID,0).getValue();
    	document.getElementById("colorSet").value = mygrid.cellById(rowID,1).getValue();
    	document.getElementById("hardwareVersion").value = mygrid.cellById(rowID,2).getValue();
    	document.getElementById("firmwareVersion").value = mygrid.cellById(rowID,3).getValue();
    	document.getElementById("printed_Id").value = mygrid.cellById(rowID,4).getValue();
    	document.getElementById("notes").value = mygrid.cellById(rowID,6).getValue();

       	//reset select Box
    	document.getElementById("selectColor")[0].selected = "1";

       	//reset radio button
       	resetRadioButton();
       	
       	var assignedVal = mygrid.cellById(rowID,5).getValue();
       	if(assignedVal == "Assigned")
       	{
       		document.getElementById("update").disabled = true;
       		document.getElementById("delete").disabled = true;
       		document.getElementById("isAssignedHidden").value='1';
       	}
       	else
       		{
       		document.getElementById("update").disabled = false;
   			document.getElementById("delete").disabled = false;
   			var d = document.getElementById("isAssignedHidden");
       		document.getElementById("isAssignedHidden").value='0';
       		}

       	makeAllfieldDisabled();
    }
    
    function makeAllfieldDisabled()
    {
       	document.getElementById("wocketId").style.background= "#D9D9D9";
    	document.getElementById("colorSet").style.background= "#D9D9D9";
    	document.getElementById("hardwareVersion").style.background= "#D9D9D9";
    	document.getElementById("firmwareVersion").style.background= "#D9D9D9";
    	document.getElementById("printed_Id").style.background= "#D9D9D9";
    	document.getElementById("notes").style.background= "#D9D9D9";

    	document.getElementById("selectColor").disabled = true;
    	document.getElementById("wocketId").readOnly = true;
    	document.getElementById("colorSet").readOnly = true;
    	document.getElementById("hardwareVersion").readOnly = true;
    	document.getElementById("firmwareVersion").readOnly = true;
    	document.getElementById("printed_Id").readOnly = true;
    	document.getElementById("notes").readOnly = true;
    }
    
    function makeAllfieldEnabled()
    {
       	document.getElementById("wocketId").style.background= "#FCFCFC";
    	document.getElementById("colorSet").style.background= "#FCFCFC";
    	document.getElementById("hardwareVersion").style.background= "#FCFCFC";
    	document.getElementById("firmwareVersion").style.background= "#FCFCFC";
    	document.getElementById("printed_Id").style.background= "#FCFCFC";
    	document.getElementById("notes").style.background= "#FCFCFC";

    	document.getElementById("selectColor").disabled = false;
    	document.getElementById("wocketId").readOnly = false;
    	document.getElementById("colorSet").readOnly = false;
    	document.getElementById("hardwareVersion").readOnly = false;
    	document.getElementById("firmwareVersion").readOnly = false;
    	document.getElementById("printed_Id").readOnly = false;
    	document.getElementById("notes").readOnly = false;
    }
    function clearAllTextField()
    {
 		document.getElementById("wocketId").value = "";
 		document.getElementById("colorSet").value="";
  		document.getElementById("hardwareVersion").value="";
  		document.getElementById("firmwareVersion").value="";
  		document.getElementById("printed_Id").value="";
  		document.getElementById("notes").value="";
  		    	
  		document.getElementById("isAssigendHidden").value="0";
    }
    
    //generate error label
    function createErrorLabel(message,parent)
    {
    	var errorLabel = document.createElement('label');
   		errorLabel.setAttribute('id',"errorLabel");
   		errorLabel.innerHTML= message;
   		errorLabel.style.color = 'red';
   		parent.appendChild(errorLabel);
    }
    //reset all radio button
    function resetRadioButton()
    {
       	for (var i=0; i<document.getElementsByName("select").length; i++)
    		document.getElementsByName("select")[i].checked = false;
    }
    
    
    //radio button onClick event
function radioButtonClick(radioValue)
{
	
	document.getElementById("action").value = radioValue;//set radio button value to hidden field
	//1 for add 2 for update and 3 for delete	
	switch(radioValue)
		{
		case '1':
			makeAllfieldEnabled();
			clearAllTextField();
	    	mygrid.clearSelection();
			break;
		case '2':
			if(!mygrid.getSelectedRowId())
				alert("Please select wocket from wocket table for update.");
			else{
				makeAllfieldEnabled();
				document.getElementById("wocketId").readOnly = true;
				document.getElementById("wocketId").style.background= "#D9D9D9";
			}
			break;
		case '3':
			if(!mygrid.getSelectedRowId())
				alert("Please select wocket from wocket table for delete.");
			else
			{
				doOnRowSelected(mygrid.getSelectedRowId());
				document.getElementsByName("select")[2].checked = true;
			}
		}
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

function submitWocket()
{	

	var errorDiv = document.getElementById("errorDiv");
   	var label = document.getElementById("errorLabel");
	if(label)
		errorDiv.removeChild(label);

	var radioValue=checkRadioButton();
	
   	//reset radio button
   	resetRadioButton();
	
	if( document.getElementById("wocketId").value==""||
		document.getElementById("colorSet").value == ""||
		document.getElementById("hardwareVersion").value == ""||
		document.getElementById("firmwareVersion").value == ""||
		document.getElementById("printed_Id").value == "")
			createErrorLabel("All fields are mendatory.",errorDiv);
   	else if(radioValue=="")
   		createErrorLabel("Select type of action before submit.",errorDiv);
   		
	else
		document.wocketForm.submit(); 
}

function setColor(colorValue)
{
	if(colorValue != "")
		document.getElementById("colorSet").value = colorValue;

}

    </script>
</head>
<body onload="doInitGrid();">
<h3>Wockets Directory</h3>
<div id="Wocketsgrid_container" style="width:720px;height:200px;"></div>
<h4>Manage Wockets</h4>

<div id="errorDiv"></div>
<form:form action="submitWockets.html" commandName="wocket" name="wocketForm" method="get">
<table>
<tr><td>Select:</td>
<td><input type="radio" name="select" value="1" onclick="radioButtonClick(this.value);" checked="checked"/>Add
<input type="radio" name="select" value="2" id="update" onclick="radioButtonClick(this.value);"/>Update
<input type="radio" name="select" value="3" id="delete" onclick="radioButtonClick(this.value);"/>Delete</td>
</tr>
<tr>
<td><label>Wocket Id:</label></td><td><form:input path="wocketId" id="wocketId"/></td>
</tr>
<tr>
<td><label>Color Set:</label></td><td><form:input path="colorSet" id="colorSet" size="5"/>
<select id="selectColor" onchange="setColor(this.value);">
<option value="">--Select--</option>
<option value="Green">Green</option>
<option value="Red">Red</option>
</select>
<td><label>Hardware Version</label></td><td><form:input path="hardwareVersion" id="hardwareVersion"/></td>
</tr>
<tr>
<td><label>Firmware Version</label></td><td><form:input path="firmwareVersion" id="firmwareVersion"/></td>
<td><label>Printed Id:</label></td><td><form:input path="printed_Id" id="printed_Id" value="" maxlength="1"/>
<form:hidden path="isAssigned" id="isAssignedHidden" value="0"/>
<input type="hidden" id="action" name="action" value="1"/>
</td>
</tr>
<tr>
<td><label>Notes:</label></td><td colspan="3"><form:textarea path="notes" id="notes" cols="30" rows="6"/></td>
</tr>
<tr>
<td></td><td><input type="button" value="Submit" onclick="submitWocket();"/></td>
</tr>
</table>
</form:form>
<br/><br/><br/><br/><br/><br/><br/>
</body>
</html>