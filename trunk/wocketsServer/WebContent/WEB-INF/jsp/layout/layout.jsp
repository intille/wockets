<%@ page language="java" contentType="text/html; charset=ISO-8859-1"
    pageEncoding="ISO-8859-1"%>
<%@ taglib uri="http://tiles.apache.org/tags-tiles" prefix="tiles"%>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=ISO-8859-1">
<title><tiles:insertAttribute name="title" ignore="true" /></title>
<link rel="stylesheet" type="text/css" href="css/layout.css" />
<link rel="stylesheet" type="text/css" href="css/color.css" />

<link rel="STYLESHEET" type="text/css" href="dhtmlx/dhtmlxgrid.css"/>
  <link rel="STYLESHEET" type="text/css" href="css/loadScreen.css">
    <script src="dhtmlx/dhtmlxcommon.js"></script>
    <script src="dhtmlx/dhtmlxgrid.js"></script>
    <script src="dhtmlx/dhtmlxgridcell.js"></script>
    <script src="js/AjaxRequest.js"></script>
    <script src="js/commonFunction.js"></script>
</head>

<body>

<!-- header -->
<tiles:insertAttribute name="header" />
<h1 id="top">Wockets</h1>




<!-- left menu -->
<div id="inside">
<tiles:insertAttribute name="menu" />

<!-- main body -->
<div id="content">
<tiles:insertAttribute name="body" />
</div>

</div><!-- end of inside -->

<!-- footer -->
<tiles:insertAttribute name="footer" />


</body>
</html>
