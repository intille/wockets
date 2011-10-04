<%@ page language="java" contentType="text/html; charset=ISO-8859-1"
    pageEncoding="ISO-8859-1"%>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=ISO-8859-1">
<title>Wockets - Study Directory</title>
  <link rel="STYLESHEET" type="text/css" href="dhtmlx/dhtmlxgrid.css"/>
  <link rel="STYLESHEET" type="text/css" href="css/loadScreen.css">
    <script src="dhtmlx/dhtmlxcommon.js"></script>
    <script src="dhtmlx/dhtmlxgrid.js"></script>
    <script src="dhtmlx/dhtmlxgridcell.js"></script>
    <script type="text/javascript">
    var mygrid;
    function doInitGrid(){
    	mygrid = new dhtmlXGridObject('studygrid_container');
        mygrid.setImagePath("dhtmlx/imgs/");
        mygrid.setHeader("Study Id,Description");
        mygrid.setInitWidths("100,*");
        mygrid.setColAlign("left,left");
        mygrid.setSkin("light");
        mygrid.setColSorting("str,str");
        mygrid.setColTypes("ro,ro");
        mygrid.init();
        mygrid.attachEvent("onRowSelect",doOnRowSelected);
  	    mygrid.load("getStudyList.html","json");
    }
    

    function submitStudy()
    {	
       	var studyId = document.getElementById("studyId").value;
    	var desc = document.getElementById("desc").value;
    	var errorDiv = document.getElementById("errorDiv");
    	//set all field to normal state
    	document.getElementById("studyId").value = "";
    	document.getElementById("desc").value="";
    	document.getElementById("studyId").readonly = false; 
    	document.getElementById("studyId").style.background= "#FCFCFC";
    	document.getElementById("desc").readonly = false; 
    	document.getElementById("desc").style.background= "#FCFCFC";

       	var label = document.getElementById("errorLabel");
    	if(label)
    	{
    		errorDiv.removeChild(label);
    	}
    	
    	
    	var radioValue=checkRadioButton();
    	
       	//reset radio button
       	resetRadioButton();
    	
    	if(studyId ==""||desc=="")
    	{
    		createErrorLabel("All fields are mendatory.",errorDiv);
    	}
       	else if(radioValue=="")
       		{
       		createErrorLabel("Select type of action before submit.",errorDiv);
       		}
    	else
    		{
    		//else send Ajax request
    			var xmlHttp = null;
	   			if(window.ActiveXObject)
    			{
    				xmlHttp=new ActiveXObject("Microsoft.XMLHTTP");
    			}
    			else if(window.XMLHttpRequest)
    			{
    				xmlHttp=new XMLHttpRequest();
    			 }
    			xmlHttp.onreadystatechange=function()
    			{
    				if (xmlHttp.readyState==4 && xmlHttp.status==200)
    			    {
      					if(xmlHttp.responseText == "true")
      						refreshGrid();
      					else
      						createErrorLabel("Study Id already exist, please enter another Study Id",errorDiv);
      					document.getElementById("loading").className = "loading-invisible";

       			     }
    			 }
    			xmlHttp.open("GET","submitStudy.html?studyId="+studyId+"&desc="+desc+"&actionType="+radioValue,true);
  				xmlHttp.send();
  				//visiable loading div
  				document.getElementById("loading").className = "loading-visible";
    		
        		}
    }
    function refreshGrid()
    {
    	mygrid.selectAll();
    	mygrid.deleteSelectedItem();
    	mygrid.load("getStudyList.html","json");
    }
    function doOnRowSelected(rowID)
    {
    	var id = mygrid.cellById(rowID,0);
    	var  desc= mygrid.cellById(rowID,1);
    	document.getElementById("studyId").value = id.getValue();
    	document.getElementById("desc").value = desc.getValue();
       	//reset radio button
       	resetRadioButton();
    	document.getElementById("studyId").readOnly = true; 
    	document.getElementById("studyId").style.background= "#D9D9D9";
    	document.getElementById("desc").readOnly = true; 
    	document.getElementById("desc").style.background= "#D9D9D9";
       	
    	
    }
    function createErrorLabel(message,parent)
    {
    	var errorLabel = document.createElement('label');
		errorLabel.setAttribute('id',"errorLabel");
		errorLabel.innerHTML= message;
		errorLabel.style.color = 'red';
		parent.appendChild(errorLabel);
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
    
    function radioButtonClick(radioValue)
    {
		//1 for add 2 for update and 3 for delete	
    	switch(radioValue)
			{
			case '1':
		    	document.getElementById("studyId").value = "";
		    	document.getElementById("desc").value="";
		    	document.getElementById("studyId").readOnly = false;
		    	document.getElementById("desc").readOnly = false; 
		    	document.getElementById("studyId").style.background= "#FCFCFC";
		    	document.getElementById("desc").style.background= "#FCFCFC";
		    	mygrid.clearSelection();
				break;
			case '2':
				if(document.getElementById("studyId").value == "")
					{
					alert("Please select study from study table for update.");
					//reset radio button
					resetRadioButton();
					}
				else{
		    	document.getElementById("studyId").readOnly = true;
		    	document.getElementById("desc").readOnly = false;
		    	document.getElementById("studyId").style.background= "#D9D9D9";
		    	document.getElementById("desc").style.background= "#FCFCFC";
		    	mygrid.clearSelection();
				}
				break;
			case '3':
				if(!mygrid.getSelectedRowId())
					{
			    	document.getElementById("studyId").value = "";
			    	document.getElementById("desc").value = "";
					alert("Please select study from study table for delete.");
					resetRadioButton();
					}
				else
				{
			    	var rowID = mygrid.getSelectedRowId();
					var id = mygrid.cellById(rowID,0);
			    	var  desc= mygrid.cellById(rowID,1);
			    	document.getElementById("studyId").value = id.getValue();
			    	document.getElementById("desc").value = desc.getValue();
					document.getElementById("studyId").readOnly = true; 
			    	document.getElementById("studyId").style.background= "#D9D9D9";
			    	document.getElementById("desc").readOnly = true; 
			    	document.getElementById("desc").style.background= "#D9D9D9";
				}
			}
    }
    function resetRadioButton()
    {
       	for (var i=0; i<document.getElementsByName("select").length; i++)
    		document.getElementsByName("select")[i].checked = false;
    }
    
    </script>
</head>
<body onload="doInitGrid();">
<h3>Study Directory</h3>

	<div id="studygrid_container" style="width:400px;height:150px;"></div>
	<div id="loading" class="loading-invisible">
	&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;
	<img alt="Loading..." src="img/loading.gif" style="position: absolute; top: 25%; left: 60%;"></div>
    

<h4>Manage Study</h4>
<form name="newStudy">
<div id="errorDiv"></div>
<table>
<tr><td>Select:</td>
<td><input type="radio" name="select" value="1" onclick="radioButtonClick(this.value);" checked="checked"/>Add
<input type="radio" name="select" value="2" onclick="radioButtonClick(this.value);"/>Update
<input type="radio" name="select" value="3" onclick="radioButtonClick(this.value);"/>Delete</td>
</tr>
<tr><td><label>Study Id:</label></td><td><input type=text id="studyId"/></td></tr>
<tr><td><label>Description:</label></td><td><input type=text id="desc"/></td></tr>
<tr><td></td><td><input type="button" value="Submit" onclick="submitStudy();"/></td></tr>
</table>
</form>
<br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/>
</body>
</html>