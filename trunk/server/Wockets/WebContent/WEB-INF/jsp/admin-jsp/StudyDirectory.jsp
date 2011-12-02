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
  	    
  	    //get Review CheckList
  	 	getReviewerCheckList();
    }
    

    function submitStudy()
    {	
       	var studyId = document.getElementById("studyId").value;
    	var desc = document.getElementById("desc").value;
    	var selectedReviewCheck = getSelectedCheckList();
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
    	
    	if(studyId ==""||desc=="" || selectedReviewCheck=="")
    	{
    		createErrorLabel("All * mark fields are mendatory.",errorDiv);
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
      					{
      						refreshGrid();
      						refreshCheckList();
      					}
      					else
      						createErrorLabel("Study Id already exist, please enter another Study Id",errorDiv);
      					document.getElementById("loading").className = "loading-invisible";

       			     }
    			 }
    			xmlHttp.open("GET","submitStudy.html?studyId="+studyId+"&desc="+desc+"&selectedReviewCheck="+selectedReviewCheck+"&actionType="+radioValue,true);
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
    	
    	//for CheckList table
    	refreshCheckList();
    	getAssignedCheckList();
       	
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
		    	refreshCheckList();
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
    
    //*************CheckList******************
    //Ajax for reviewer checkList
    function getReviewerCheckList()
    {
    	var xmlHttp = getAjaxGETRequest();
    	xmlHttp.onreadystatechange=function()
    	  {
    	  	if (xmlHttp.readyState==4 && xmlHttp.status==200)
    	    {
    	    	var reviewerCheckList = eval(xmlHttp.responseText);
    	    	addCheckListRow(reviewerCheckList);
    	    }
    	  }
    	xmlHttp.open("POST","getReviewerChecklist.html",false);
    	xmlHttp.send();
    	
    }
    //add rows for available checkList into DOM table
    function addCheckListRow(reviewerCheckList)
    {
    	var table = document.getElementById("checkList");
    	for(var i=0; i<reviewerCheckList.length; i++)
    	{
     		var check = reviewerCheckList[i];
    		addToTable(check.checkId, check.parameter,"checkList");
    	}

    }
    //add row to checklist table
    function addToTable(id,value,tableId)
    {
    	var table = document.getElementById(tableId);
    	var rowNbr = table.getElementsByTagName('tr').length;
		var row = table.insertRow(rowNbr);
		row.id = rowNbr;
		var td1 = document.createElement('td');
		var checkBox = document.createElement('input'); 
		checkBox.type = 'checkbox';
		checkBox.value = id;
		checkBox.name = "checkGroup";
		checkBox.onclick = function(){selectRow(checkBox)};
		if(rowNbr < 6)//checked first 6 check box
			checkBox.checked = true;
		td1.appendChild(checkBox);
		
		var td2 = document.createElement('td');
		td2.innerHTML = value;
		
		row.appendChild(td1);
		row.appendChild(td2);

    }
    //add new check to list DB
    function addNewCheck()
    {
    	var newCheck = document.getElementById("newCheck").value;
    	var id;
    	if(newCheck != "")
    	{
    		var xmlHttp = getAjaxGETRequest();
        	xmlHttp.onreadystatechange=function()
        	  {
        	  	if (xmlHttp.readyState==4 && xmlHttp.status==200)
        	    {
        	  		id = xmlHttp.responseText;//get Id from server
            		addToTable(id,newCheck,"checkList");
            		document.getElementById("newCheck").value = "";
        	    }
        	  }
        	xmlHttp.open("GET","addNewCheck.html?newCheck="+newCheck,true);
        	xmlHttp.send();
       }
    }
    
  //refresh checklist
    function refreshCheckList()
    {
    	document.getElementById("checkList").innerHTML = "";
    	getReviewerCheckList();
    }
  //get all checked Box values
  function getSelectedCheckList()
  {
	  var checkIds ="";
	  var checkBoxs = document.getElementsByName("checkGroup");
	  for(var i=0; i<checkBoxs.length;i++)
	  {
		  var check = checkBoxs[i];
		if(check.checked)
			checkIds += check.value+":";
      }
	  return checkIds;
  }
  //get all assign checkList for selected study
  function getAssignedCheckList()
  {
	  var studyId = document.getElementById("studyId").value;
	  if(studyId !="")
	  {
	 	 var xmlHttp = getAjaxGETRequest();
  		xmlHttp.onreadystatechange=function()
  	  	{
  	  		if (xmlHttp.readyState==4 && xmlHttp.status==200)
  	    	{
  	  			var ids = eval(xmlHttp.responseText);//get Id from server
  	  		    checkAssignedCheckBox(ids);
  	    	}
  	  	}
  		xmlHttp.open("GET","getStudyAssignedCheckList.html?studyId="+studyId,true);
  		xmlHttp.send();
	 }
  }
  
//add contains method to Array object
  Array.prototype.contains = function(obj) 
  {
	var result =false;    
	var i = this.length-1;
	    while (i>=0) {
	        if (this[i] == obj) {
	        	result =  true;
	            break;
	        }
	        i--;
	    }
	    return result;
  }
  function checkAssignedCheckBox(ids)
  {
	  var checkBoxs = document.getElementsByName("checkGroup");
	  for(var i=0; i<checkBoxs.length;i++)
	  {
		  var check = checkBoxs[i];
		  var result = ids.contains(check.value);
		  if(result)
			  check.checked = true;
		  else
			  check.checked = false;
      }
	  
  }
  

  //******************end CheckList*******************
    
    //checkBox onClick event
    function selectRow(checkBox)
    {
    	var color = "";
    	if(checkBox.checked)
    		color = "#D9D9D9";
    	var cell = checkBox.parentNode;
    	var row = cell.parentNode;
    	row.style.background= color;
    }
    
    //delete selected Check from checklist table
    function deleteCheck()
    {
    	var checkBoxs = document.getElementsByName("checkGroup");
    	var x = 0;
    	var rowId= [];
    	for(var i=0; i<checkBoxs.length; i++)
    	{
    		var checkBox = checkBoxs[i];
    		if(checkBox.checked)
    		{
    			rowId[x] = checkBox.parentNode.parentNode.id;
    			x++;
    		}
      	}
     	deleteFromTable(rowId,"checkList");
    }
    //remove from table
    function deleteFromTable(rowId,tableId)
    {
    	var table = document.getElementById(tableId);
    	for(var n=0; n<rowId.length; n++ )
    	{
    		row = document.getElementById(rowId[n]);
    		row.parentElement.removeChild(row);
    		
    	}
    }
</script>

<style type="text/css">
.mandatory{
color:#ff0000;
}
</style>
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
<tr><td><label>Study Id:</label><label class="mandatory">*</label></td><td><input type=text id="studyId"/></td></tr>
<tr><td><label>Description:</label><label class="mandatory">*</label></td><td><input type=text id="desc"/></td></tr>
</table>

<h4 style="margin-bottom: 0em;">Reviewer Checklist:</h4>
<label class="mandatory">* Select at least one review question</label><br/>
<input type="button" value="Refresh Checklist" onclick="refreshCheckList()"/>
<div style="border:1px solid black;width: 400px;">
<table id="checkList"></table>
</div>
<table>
<tr><td><input type="button" value="Delete Selected" onclick="deleteCheck()"/></td></tr>
<tr><td><h5>Add New Check:</h5></td></tr>
<tr>
<td><input type="text" name="newCheck" id="newCheck" maxlength="450" size="50"/></td>
<td><input type="button" value="  Add  " onclick="addNewCheck()"/></td>
</tr>
<tr><td>&nbsp;</td></tr>
<tr><td colspan="2"><center><input type="button" value="      Submit      " onclick="submitStudy();"/></center></td></tr>
</table>



</form>


<br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/>
</body>
</html>