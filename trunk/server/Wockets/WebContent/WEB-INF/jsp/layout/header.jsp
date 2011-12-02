<%@ page language="java" contentType="text/html; charset=ISO-8859-1"
    pageEncoding="ISO-8859-1"%>
    <%@taglib prefix="c" uri="http://java.sun.com/jsp/jstl/core" %>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<title></title>
</head>
<body>

<div id="perm-links">
<ul>
<li><a href="home.html">Home</a></li>
<c:choose>
<c:when test="${sessionScope.UserRole== null}">
<li><a href="loginPage.html">Login</a></li>
</c:when>
<c:otherwise>
<li><a href="logout.html">Logout</a></li>
</c:otherwise>
</c:choose>

<li><a href="#">Contact</a></li>
</ul>
</div>

</body>
</html>