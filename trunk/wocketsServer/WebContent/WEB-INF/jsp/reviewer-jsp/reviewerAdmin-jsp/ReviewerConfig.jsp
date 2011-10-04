<%@ page language="java" contentType="text/html; charset=ISO-8859-1"
    pageEncoding="ISO-8859-1"%>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=ISO-8859-1">
<title>Wocket - Reviewer Config</title>
<script type="text/javascript">
function test(){
var xmlHttp= getAjaxGETRequest();
	xmlHttp.onreadystatechange=function()
	{
		if (xmlHttp.readyState==4 && xmlHttp.status==200)
		{
			alert(xmlHttp.responseText);
	    }
	  };
	
	  xmlHttp.open("GET","isAndroidDataLogValid.html",true);
	  xmlHttp.send();
	  }
	  </script>
</head>
<body>
<h2>General Configuration</h2>
<input type="button" value="test" onclick="test()"/>
</body>
</html>