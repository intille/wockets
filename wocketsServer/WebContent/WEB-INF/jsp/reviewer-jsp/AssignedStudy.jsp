<%@ page language="java" contentType="text/html; charset=ISO-8859-1"
    pageEncoding="ISO-8859-1"%>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=ISO-8859-1">
<title>Wockets - Assigned Study</title>
    <script type="text/javascript">
    var mygrid;
    function doInitGrid(){
    	mygrid = new dhtmlXGridObject('assignedStudy_Container');
        mygrid.setImagePath("dhtmlx/imgs/");
        mygrid.setHeader("Study Id,Description");
        mygrid.setInitWidths("100,*");
        mygrid.setColAlign("left,left");
        mygrid.setSkin("light");
        mygrid.setColSorting("str,str");
        mygrid.setColTypes("ro,ro");
        mygrid.init();
  	    mygrid.load("reviewerGetAssignedStudy.html","json");
    }
    </script>

</head>
<body onload="doInitGrid()">
<h3>Assigned Study</h3>
<div id="assignedStudy_Container" style="width:400px;height:150px;"></div>
</body>
<br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/>
</html>