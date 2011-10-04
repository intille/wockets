<%@ page language="java" contentType="text/html; charset=ISO-8859-1"
    pageEncoding="ISO-8859-1"%>
    <%@taglib uri="http://www.springframework.org/tags/form" prefix="form"%>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=ISO-8859-1">
<title>Wockets - Phone Directory</title>
  <link rel="STYLESHEET" type="text/css" href="dhtmlx/dhtmlxgrid.css">
    <script src="dhtmlx/dhtmlxcommon.js"></script>
    <script src="dhtmlx/dhtmlxgrid.js"></script>
    <script src="dhtmlx/dhtmlxgridcell.js"></script>
    <script type="text/javascript">
    var mygrid;
    function doInitGrid(){
    	mygrid = new dhtmlXGridObject('Phonegrid_container');//create grid object
        mygrid.setImagePath("dhtmlx/imgs/");
        mygrid.setHeader("IMEI,Phone Model,Platform,OS Version,App Version,Is Assigned");
        mygrid.setInitWidths("120,120,120,120,120,120");
        mygrid.setColAlign("left,left,left,left,left,left");
        mygrid.setSkin("light");
        mygrid.setColSorting("str,str,str,str,str,str");
        mygrid.setColTypes("ro,ro,ro,ro,ro,ro");
        mygrid.init();
        mygrid.attachEvent("onRowSelect",doOnRowSelected);
        mygrid.load("getPhoneDirectory.html","json");
        clearAllTextField();
   }
    
    function doOnRowSelected(rowID)
    {
    	//mygrid.setRowTextStyle(rowID,"background-color: #D9D9D9");
    	
    	var IMEI= mygrid.cellById(rowID,0);
    	var phoneModel= mygrid.cellById(rowID,1);
    	var platform= mygrid.cellById(rowID,2);
    	var OSVersion= mygrid.cellById(rowID,3);
    	var appVersion = mygrid.cellById(rowID,4);
    	var isAssigend = mygrid.cellById(rowID,5);

    	document.getElementById("IMEI").value = IMEI.getValue();
    	document.getElementById("phoneModel").value = phoneModel.getValue();
    	document.getElementById("platform").value = platform.getValue();
    	document.getElementById("OSVersion").value = OSVersion.getValue();
    	document.getElementById("appVersion").value = appVersion.getValue();

       	//reset select Box
    	document.getElementById("selectPlatform")[0].selected = "1";

       	//reset radio button
       	resetRadioButton();
       	
       	var assignedVal = isAssigend.getValue();
       	if(assignedVal == "Assigned")
       	{
       		document.getElementById("update").disabled = true;
       		document.getElementById("delete").disabled = true;
       		document.getElementById("isAssigendHidden").value='1';
       	}
       	else
       		{
       		document.getElementById("update").disabled = false;
   			document.getElementById("delete").disabled = false;
       		document.getElementById("isAssigendHidden").value='0';
       		}
    	
       	document.getElementById("IMEI").style.background= "#D9D9D9";
    	document.getElementById("phoneModel").style.background= "#D9D9D9";
    	document.getElementById("platform").style.background= "#D9D9D9";
    	document.getElementById("OSVersion").style.background= "#D9D9D9";
    	document.getElementById("appVersion").style.background= "#D9D9D9";

    	document.getElementById("selectPlatform").disabled = true;
    	document.getElementById("IMEI").readOnly = true;
    	document.getElementById("phoneModel").readOnly = true;
    	document.getElementById("platform").readOnly = true;
    	document.getElementById("OSVersion").readOnly = true;
    	document.getElementById("appVersion").readOnly = true;
       	
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
   		//1 for add 2 for update and 3 for delete	
    	switch(radioValue)
   			{
   			case '1':
   				clearAllTextField();
   		    	
   		    	document.getElementById("IMEI").readOnly = false;
   		    	document.getElementById("phoneModel").readOnly = false;
   		    	document.getElementById("platform").readOnly = false;
   		    	document.getElementById("OSVersion").readOnly = false;
   		    	document.getElementById("appVersion").readOnly = false;
   		    	document.getElementById("selectPlatform").disabled = false;
   		    	
   		    	document.getElementById("IMEI").style.background= "#FCFCFC";
   		    	document.getElementById("phoneModel").style.background= "#FCFCFC";
   		    	document.getElementById("platform").style.background= "#FCFCFC";
   		    	document.getElementById("OSVersion").style.background= "#FCFCFC";
   		    	document.getElementById("appVersion").style.background= "#FCFCFC";
   		    	
   		    	document.getElementById("action").value='1';
   		    	
   		    	mygrid.clearSelection();
   				break;
   			case '2':
   				if(!mygrid.getSelectedRowId())
   					{
   					alert("Please select phone from phone table for update.");
   					//reset radio button
   					resetRadioButton();
   					}
   				else{
   					document.getElementById("IMEI").readOnly = true;
   			    	document.getElementById("phoneModel").readOnly = false;
   			    	document.getElementById("platform").readOnly = false;
   			    	document.getElementById("OSVersion").readOnly = false;
   			    	document.getElementById("appVersion").readOnly = false;
   			    	document.getElementById("selectPlatform").disabled = false;
   			    	
   			    	document.getElementById("IMEI").style.background= "#D9D9D9";
   			    	document.getElementById("phoneModel").style.background= "#FCFCFC";
   			    	document.getElementById("platform").style.background= "#FCFCFC";
   			    	document.getElementById("OSVersion").style.background= "#FCFCFC";
   			    	document.getElementById("appVersion").style.background= "#FCFCFC";
   			    	
   			    	document.getElementById("action").value='2';
   		    		
   			    	mygrid.clearSelection();
   					}
   				break;
   			
   			case '3':
   				if(!mygrid.getSelectedRowId())
   					{
   					clearAllTextField();
   			    	alert("Please select phone from phone table for delete.");
   					resetRadioButton();
   					}
   				else
   				{
   			    	document.getElementById("IMEI").style.background= "#D9D9D9";
   			    	document.getElementById("phoneModel").style.background= "#D9D9D9";
   			    	document.getElementById("platform").style.background= "#D9D9D9";
   			    	document.getElementById("OSVersion").style.background= "#D9D9D9";
   			    	document.getElementById("appVersion").style.background= "#D9D9D9";
   			    	
   			    	document.getElementById("IMEI").readOnly = true;
   			    	document.getElementById("phoneModel").readOnly = true;
   			    	document.getElementById("platform").readOnly = true;
   			    	document.getElementById("OSVersion").readOnly = true;
   			    	document.getElementById("appVersion").readOnly = true;
   			    	document.getElementById("selectPlatform").disabled = true;
   			    	
   			    	document.getElementById("action").value='3';
   			    	
   			    	mygrid.clearSelection();
   				}
   			}
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
    
 //select comboBox on change event
 function setPhonePlatform()
 {
	 var selectBox = document.getElementById("selectPlatform");
	 var selectValue = selectBox.options[selectBox.selectedIndex].value; 
	 if(!selectValue=="")
		{
	 		document.getElementById("platform").value= selectValue;
		}
 }
 
 //submit form
  function submitPhone()
 {	
	       	var IMEI = document.getElementById("IMEI").value;
	    	var phoneModel = document.getElementById("phoneModel").value;
	    	var platform = document.getElementById("platform").value;
	    	var OSVersion = document.getElementById("OSVersion").value;
	    	var appVersion = document.getElementById("appVersion").value;

	    	
	    	var errorDiv = document.getElementById("errorDiv");
	    	var label = document.getElementById("errorLabel");
	    	if(label)
	    	{
	    		errorDiv.removeChild(label);
	    	}
	    	
	    	var radioValue=checkRadioButton();
	    	
	       	//reset radio button
	       	resetRadioButton();
	    	
	    	if(IMEI ==""|| phoneModel =="" ||platform=="" || OSVersion=="" || appVersion=="")
	    	{
	    		createErrorLabel("All fields are mendatory.",errorDiv);
	    	}
	       	else if(radioValue=="")
	       		{
	       		createErrorLabel("Select type of action before submit.",errorDiv);
	       		}
	    	else
	    		{
   				//submit form
	    		document.phoneForm.submit(); 
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
  
  function clearAllTextField()
  {
	    	    document.getElementById("IMEI").value = "";
		    	document.getElementById("phoneModel").value="";
		    	document.getElementById("platform").value="";
		    	document.getElementById("OSVersion").value="";
		    	document.getElementById("appVersion").value="";
		    	
		    	document.getElementById("isAssigendHidden").value="0";
  }
    
    
     </script>
</head>
<body onload="doInitGrid();">
<h3>Phone Directory</h3>
<div id="Phonegrid_container" style="width:720px;height:200px;"></div>

<h3>Manage Phone</h3>

<div id="errorDiv"></div>
<form:form action="submitPhone.html" commandName="phone" name="phoneForm" method="get">
<table>
<tr><td>Select:</td>
<td><input type="radio" name="select" value="1" onclick="radioButtonClick(this.value);" checked="checked"/>Add
<input type="radio" name="select" value="2" id="update" onclick="radioButtonClick(this.value);"/>Update
<input type="radio" name="select" value="3" id="delete" onclick="radioButtonClick(this.value);"/>Delete</td>
</tr>

<tr>
<td><label>IMEI:</label></td><td><form:input path="IMEI" id="IMEI"/></td>
<td><label>Phone Model:</label></td><td><form:input path="phoneModel" id="phoneModel"/></td>
</tr>
<tr>
<td><label>Platform:</label></td>
<td>
<form:input path="platform" id="platform" size="6"/>
<select id="selectPlatform" onchange="setPhonePlatform();">
<option value="">--Select--</option>
<option value="Window">Window</option>
<option value="Android">Android</option>
</select>
</td>
<td><label>OS Version:</label></td><td><form:input path="OSVersion" id="OSVersion"/></td>
</tr>
<tr>
<td><label>App Version:</label></td><td><form:input path="appVersion" id="appVersion"/>
<form:hidden path="isAssigned" id ="isAssigendHidden" value="0"/>
<input type="hidden" name="action" id="action" value="1"/>
</td>
</tr>
<tr>
<td></td><td><input type="button" value="Submit" onclick="submitPhone();"/></td>
</tr>
</table>
</form:form>
<br/><br/><br/><br/><br/><br/><br/><br/><br/><br/>
</body>
</html>