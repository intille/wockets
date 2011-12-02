<%@ page language="java" contentType="text/html; charset=ISO-8859-1"
    pageEncoding="ISO-8859-1"%>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=ISO-8859-1">
<title>Wockets - Participant Directory</title>
<script type="text/javascript">
    var mygrid;
    function doInitGrid(){
    	mygrid = new dhtmlXGridObject('ParticipantGrid_container');//create grid object
        mygrid.setImagePath("dhtmlx/imgs/");
        mygrid.setHeader("Participant Id,First Name,Last Name,Gender,Email,Is Active");
        mygrid.setInitWidths("120,120,120,120,120,*");
        mygrid.setColAlign("left,left,left,left,left,left");
        mygrid.setSkin("light");
        mygrid.setColSorting("str,str,str,str,str,str");
        mygrid.setColTypes("ro,ro,ro,ro,ro,ro");
        mygrid.init();
       mygrid.attachEvent("onRowSelect",doOnRowSelected);
        mygrid.load("getParticipantDirectory.html","json");
   }
    
    function doOnRowSelected(rowID)
    {
    	var pId= mygrid.cellById(rowID,0);
    	var fName= mygrid.cellById(rowID,1);
    	var lName= mygrid.cellById(rowID,2);
    	
    	document.getElementById("pId").value= pId.getValue();
    	document.getElementById("fName").value= fName.getValue();
    	document.getElementById("lName").value= lName.getValue();
    	document.getElementById("manageButton").disabled = false;
    }

    
</script>
</head>
<body onload="doInitGrid();">
<form action="manageParticipant.html" method="GET">
<h3>Participant Directory</h3>
<div id="ParticipantGrid_container" style="width:720px;height:250px;"></div>
<br/>
<table>
<tr>
<td><label>Participant Id:</label></td><td><input type="text" id="pId" name="pId" readonly="readonly" style="background-color: #D9D9D9"/></td>
</tr>
<tr>
<td><label>First Name:</label></td><td><input type="text" id="fName" readonly="readonly" style="background-color: #D9D9D9"/></td>
<td><label>Last Name:</label></td><td><input type="text" id="lName" readonly="readonly" style="background-color: #D9D9D9"/></td>
</tr>
</table>
<br/>
<table>
<tr>
<td><input type="button" value="Register New Participant" onClick="javascript:location.href = 'newParticipant.html';" /></td>
<td>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;</td>
<td><input type="submit" value="Manage Participant" id="manageButton" disabled="disabled"></td>
</tr>
</table>
</form>
<br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/>
</body>
</html>