<%@ page language="java" contentType="text/html; charset=ISO-8859-1"
    pageEncoding="ISO-8859-1"%>
    <%@taglib uri="http://www.springframework.org/tags/form" prefix="form"%>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=ISO-8859-1">
<title>Wockets - User Accounts Directory</title>
  <link rel="STYLESHEET" type="text/css" href="dhtmlx/dhtmlxgrid.css">
    <script src="dhtmlx/dhtmlxcommon.js"></script>
    <script src="dhtmlx/dhtmlxgrid.js"></script>
    <script src="dhtmlx/dhtmlxgridcell.js"></script>
    <script type="text/javascript">
    var mygrid;
    var assignedStudyGrid;
    var availabelStudyGrid;
    function doInitGrid(){
    	mygrid = new dhtmlXGridObject('UserAccountgrid_container');//create grid object
        mygrid.setImagePath("dhtmlx/imgs/");
        mygrid.setHeader("User_Id,First Name,Last Name,Email,Registration Date,User Type,User Name,Active Status");
        mygrid.setInitWidths("70,120,120,150,145,100,100,*");
        mygrid.setColAlign("left,left,left,left,left,left,left,left");
        mygrid.setSkin("light");
        mygrid.setColSorting("int,str,str,str,date,str,str,str");
        mygrid.setColTypes("ro,ro,ro,ro,ro,ro,ro,ro");
        mygrid.init();
        mygrid.attachEvent("onRowSelect",doOnRowSelected);
        mygrid.load("getUserAccountDirectory.html","json");
        
        //init study grids
        assignedStudyGrid = intiStudyGrid("studyGrid_Container");//init assigned study grid
        assignedStudyGrid.attachEvent("onRowSelect",assignedStudyGridOnRowSelect);
        availabelStudyGrid = intiStudyGrid("availabelStudyGrid_Container");
        availabelStudyGrid.load("getStudyList.html","json");
        availabelStudyGrid.attachEvent("onRowSelect",availStudyGridOnRowSelect);
}
    
    function doOnRowSelected(rowID)
    {

    	var userName= mygrid.cellById(rowID,6);
    	var fName= mygrid.cellById(rowID,1);
    	var lName= mygrid.cellById(rowID,2);
    	var email= mygrid.cellById(rowID,3);
    	var userType = mygrid.cellById(rowID,5); 
    	var activeStatus = mygrid.cellById(rowID,7);

    	document.getElementById("userName").value = userName.getTitle();
    	document.getElementById("fName").value = fName.getTitle();
    	document.getElementById("lName").value = lName.getTitle();
    	document.getElementById("email").value = email.getTitle();
    	document.getElementById("role").value = userType.getTitle();
    	document.getElementById("activeStatus").value = activeStatus.getTitle();
    	

       	//reset select Box
    	document.getElementById("selectType")[0].selected = "1";
    	document.getElementById("accountStatus")[0].selected = "1";
       	//reset radio button
       	resetRadioButton();
       	
    	document.getElementById("fName").style.background= "#D9D9D9";
    	document.getElementById("lName").style.background= "#D9D9D9";
    	document.getElementById("email").style.background= "#D9D9D9";
    	
    	document.getElementById("fName").readOnly = true;
    	document.getElementById("lName").readOnly = true;
    	document.getElementById("email").readOnly = true;
    	
    	//reset assigned study grid
    	refreshAssgStudyGrid();
    	
     }
 
 function setUserType()
 {
	 var selectBox = document.getElementById("selectType");
	 var selectValue = selectBox.options[selectBox.selectedIndex].value; 
	 if(!selectValue=="")
		{
	 		document.getElementById("role").value= selectValue;
		}
 }
 
 function setAccountStatus()
 {
	 var selectBox = document.getElementById("accountStatus");
	 var selectValue = selectBox.options[selectBox.selectedIndex].value; 
	 if(!selectValue=="")
	 {
		document.getElementById("activeStatus").value= selectValue;
	 }
 }
 
 function resetRadioButton()
 {
    	for (var i=0; i<document.getElementsByName("select").length; i++)
 		document.getElementsByName("select")[i].checked = false;
 }
 
 function radioButtonClick(radioValue)
 {
		//1 for add 2 for update and 3 for delete	
 	switch(radioValue)
			{
			case '1':
		    	document.getElementById("fName").value = "";
		    	document.getElementById("lName").value="";
		    	document.getElementById("email").value="";
		    	document.getElementById("activeStatus").value="";
		    	document.getElementById("role").value="";
		    	document.getElementById("fName").readOnly = false;
		    	document.getElementById("lName").readOnly = false;
		    	document.getElementById("email").readOnly = false;
		    	document.getElementById("fName").style.background= "#FCFCFC";
		    	document.getElementById("lName").style.background= "#FCFCFC";
		    	document.getElementById("email").style.background= "#FCFCFC";
		    	mygrid.clearSelection();
				break;
			case '2':
				if(!mygrid.getSelectedRowId())
					{
					alert("Please select user from user table for update.");
					//reset radio button
					resetRadioButton();
					}
				else{
			    	document.getElementById("fName").readOnly = false;
			    	document.getElementById("lName").readOnly = false;
			    	document.getElementById("email").readOnly = false;
			    	document.getElementById("fName").style.background= "#FCFCFC";
			    	document.getElementById("lName").style.background= "#FCFCFC";
			    	document.getElementById("email").style.background= "#FCFCFC";
		    		//mygrid.clearSelection();

					}
				break;
			case '3':
				if(!mygrid.getSelectedRowId())
					{
			    	document.getElementById("fName").value = "";
			    	document.getElementById("lName").value="";
			    	document.getElementById("email").value="";
			    	document.getElementById("activeStatus").value="";
			    	document.getElementById("role").value="";
			    	alert("Please select user from user table for delete.");
					resetRadioButton();
					}
				else
				{
					doOnRowSelected(mygrid.getSelectedRowId());
					document.getElementById("fName").style.background= "#D9D9D9";
			    	document.getElementById("lName").style.background= "#D9D9D9";
			    	document.getElementById("email").style.background= "#D9D9D9";
			    	
			    	document.getElementById("fName").readOnly = true;
			    	document.getElementById("lName").readOnly = true;
			    	document.getElementById("email").readOnly = true;
			    	document.getElementById('delete').checked = true;
			    	
			    	//mygrid.clearSelection();
					
				}
			}
 }
 
 function submitUser()
 {	
	       	var userName = document.getElementById("userName").value;
	    	var fName = document.getElementById("fName").value;
	    	var lName = document.getElementById("lName").value;
	    	var email = document.getElementById("email").value;
	    	var role = document.getElementById("role").value;
	    	var activeStatus = document.getElementById("activeStatus").value;
	    	
	    	
	    	var errorDiv = document.getElementById("errorDiv");
	    	//set all field to normal state
	    	document.getElementById("userName").value = "";
	    	document.getElementById("fName").value="";
	    	document.getElementById("lName").value="";
	    	document.getElementById("email").value="";
	    	document.getElementById("role").value="";
	    	document.getElementById("activeStatus").value="";
	    	
	    	document.getElementById("fName").style.background= "#FCFCFC";
	    	document.getElementById("lName").style.background= "#FCFCFC";
	    	document.getElementById("email").style.background= "#FCFCFC";

	       	var label = document.getElementById("errorLabel");
	    	if(label)
	    	{
	    		errorDiv.removeChild(label);
	    	}
	    	
	    	
	    	var radioValue=checkRadioButton();
	    	
	       	//reset radio button
	       	resetRadioButton();
	    	
	    	if(fName ==""||lName=="" ||email=="" || activeStatus=="" || role=="")
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
	    		//create url
	    		var url = "submitUser.html?userName="+userName+"&fName="+fName+"&lName="+lName+"&email="
	    				   +email+"&activeStatus="+activeStatus+"&role="+role+"&action="+radioValue;
	    		if(checkRadioBttValue("assignStudyRadioBtt")=="yes")
	    			url += "&concatStdId="+getAssgStdIDsConcatStr();
	    		
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
	    					refreshGrid();
	    					refreshAssgStudyGrid();
	    					document.getElementsByName("select")[0].checked = true;//checked Add radio button
	    			     }
	    			 }
    			//xmlHttp.open("GET","submitUser.html?userName="+userName+"&fName="+fName+"&lName="+lName+"&email="+email+"&activeStatus="+activeStatus+"&role="+role+"&action="+radioValue,true);
 	  			xmlHttp.open("GET",url,true);
    			xmlHttp.send();

	    		
	        		}
	    } 
 
 //Refresh the user account grid
 function refreshGrid()
 {
 	//mygrid.destructor();
 	mygrid.selectAll();
 	mygrid.deleteSelectedItem();
 	mygrid.load("getUserAccountDirectory.html","json");
 }
 

 //return the select radio button value
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
 
 //create error label
 function createErrorLabel(message,parent)
 {
 	var errorLabel = document.createElement('label');
		errorLabel.setAttribute('id',"errorLabel");
		errorLabel.innerHTML= message;
		errorLabel.style.color = 'red';
		parent.appendChild(errorLabel);
 }
 
//******change Div style to make visiable or hidden
 function changeDivStyle(divId,displayStyle)
 {	
 	document.getElementById(divId).style.display = displayStyle;
 }
 
 //*********Assign Study***************
 //init study grid
 function intiStudyGrid(divObj)
 {
		var Grid = new dhtmlXGridObject(divObj);//create grid object
		Grid.setImagePath("dhtmlx/imgs/");
		Grid.setHeader("Study Id,Description");
		Grid.setInitWidths("120,*");
		Grid.setColAlign("left,left");
		Grid.setColSorting("str,str");
		Grid.setColTypes("ro,ro");
		Grid.setSkin("light");
		Grid.init();
		return Grid;
 }
 
 //refresh assigned study Grid
 function refreshAssgStudyGrid()
 {
	assignedStudyGrid.selectAll();
	assignedStudyGrid.deleteSelectedRows();
	if(mygrid.getSelectedRowId())
	{
		var uId = mygrid.cellById(mygrid.getSelectedRowId(),0).getTitle();
		var url = "getUserAssignedStudy.html?uId="+uId;
		assignedStudyGrid.load(url,"json");
	}
 }
 
 //availabel study grid row onclick
 function availStudyGridOnRowSelect(rowID)
 {
	 document.getElementById("assignNewStudyBttn").disabled = false;
 }
 
 //assigned study grid row onclick
 function assignedStudyGridOnRowSelect(rowID)
 {
	 document.getElementById("removeStudyBttn").disabled = false;
 }
 
 
 //assign new study button onClick
 function assgnNewStudyBttnOnClick()
 {
	 var rowId = availabelStudyGrid.getSelectedRowId();
	 if(rowId)
		{
		 		
		 var studyId = availabelStudyGrid.cellById(rowId,0).getTitle();
		 
		 for(var i=0; i< assignedStudyGrid.getRowsNum();i++)
			 {
			 	if(assignedStudyGrid.cellByIndex(i, 0).getTitle() == studyId)
			 		{
			 			alert("Study already assigned.");
			 			return;
			 		
			 		}
			 }
		 var jArray = [studyId,availabelStudyGrid.cellById(rowId,1).getTitle()];
		 assignedStudyGrid.addRow(assignedStudyGrid.getRowsNum()+1,jArray);
		 
		    }//if close
	 else
		 alert("Select study from table to assign.");
 }
 
 //remove study button onClick
 function removeStudyBttnOnClick()
 {
	 assignedStudyGrid.deleteSelectedRows(); 
 }
 
 //Assign new study No radio button onClick
 function assigNewStudyNoRdBttOnClick()
 {
	 changeDivStyle('assignNewStudyDiv','none');
	 refreshAssgStudyGrid();
 }
 
 //create concat string of all assigned Study Ids using '|' delimiter
 function getAssgStdIDsConcatStr()
 {
	 var concatStr = "";
	 for(var i=0; i< assignedStudyGrid.getRowsNum();i++)
		concatStr += assignedStudyGrid.cellByIndex(i, 0).getTitle()+"|";
	 return concatStr;
}
 
//return the checked radio button value
 function checkRadioBttValue(radioName)
{
	var radioButtons = document.getElementsByName(radioName);
	var radioValue="";
	for (i=0; i<radioButtons.length; i++)
	{
		  if (radioButtons[i].checked == true)
			  radioValue = radioButtons[i].value;
  	}
	return radioValue;
}
 
 
    </script>
</head>
<body onload="doInitGrid();">
<h3>User Account Directory</h3>
<br/>
<div id="UserAccountgrid_container" style="width:860px;height:250px;"></div>

<h4>Manage User Account</h4>
<form>
<div id="errorDiv"></div>
<table>
<tr><td>Select:</td>
<td><input type="radio" name="select" value="1" id="add" onclick="radioButtonClick(this.value);" checked="checked"/>Add
<input type="radio" name="select" value="2" id="update" onclick="radioButtonClick(this.value);"/>Update
<input type="radio" name="select" value="3" id="delete" onclick="radioButtonClick(this.value);"/>Delete</td>
</tr>
<tr>
</tr>
<tr>
<td>
<input type="hidden" id="userName" name="userId"/>
<label>First Name:</label></td><td><input type="text" id="fName" maxlength="100" /></td>

<td><label>Last Name:</label></td><td><input type="text" id="lName" maxlength="100"/></td>
</tr>
<tr>
<td><label>Email:</label></td><td><input type="text"  id="email" maxlength="100"/>
</td>
<td><label>User Type:</label></td>
<td>
<input type="text" readonly="readonly" id ="role" style="background-color: #D9D9D9" size="6"/>
	<select id="selectType" onchange="setUserType();">
		<option value="">--Select--</option>
		<option value="Admin">Admin</option>
		<option value="Reviewer">Reviewer</option>
	</select>
</td>
</tr>
<tr>
<td><label>Active Status:</label></td>
<td>
<input type="text" readonly="readonly" id ="activeStatus" style="background-color: #D9D9D9" size="7"/>
	<select id="accountStatus" onchange="setAccountStatus();">
		<option value="">--Select--</option>
		<option value="Active">Active</option>
		<option value="De-Activate">De-Activate</option>
	</select>
</td>
</tr>
</table>
<br/>
<!-- Assign study -->
<label>Assign Study:</label><input type="radio" name="assignStudyRadioBtt" value="yes" onclick="changeDivStyle('studyDetail','')"/>Yes
<input type="radio" name="assignStudyRadioBtt" value="no" checked="checked" onclick="changeDivStyle('studyDetail','none')"/>No<br/>
<br/>
<div id="studyDetail" style="display: none;">
<label>Assigned Study:</label><br/>
<div id="studyGrid_Container" style="width:400px;height:100px;"></div>
<input type="button" value='Remove Selected Study' id="removeStudyBttn" disabled="disabled" onclick="removeStudyBttnOnClick()"/>
<br/>
<label>Assign New Study:</label><input type="radio" name="assignNewStudyRadioBtt" value="yes" onclick="changeDivStyle('assignNewStudyDiv','')"/>Yes
<input type="radio" name="assignNewStudyRadioBtt" value="no" checked="checked" onclick="assigNewStudyNoRdBttOnClick()"/>No<br/>
<br/>
<div id="assignNewStudyDiv" style="display: none;">
<label>Select Study:</label><br/>
<div id="availabelStudyGrid_Container" style="width:400px;height:100px;"></div>
<input type="button" value="Assign Selected Study" id="assignNewStudyBttn" disabled="disabled" onclick="assgnNewStudyBttnOnClick()"/>
<br/><br/>
</div>
 
</div>
<!-- Close Assign study -->
<br/>
<input type="button" value="    Submit    " onclick="submitUser();" style="margin-left: 150px;"/>

</form>
</body>
</html>