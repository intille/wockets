<%@ page language="java" contentType="text/html; charset=ISO-8859-1"
    pageEncoding="ISO-8859-1"%>
    <%@taglib uri="http://www.springframework.org/tags/form" prefix="form"%>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=ISO-8859-1">
<title>Insert title here</title>
</head>
<body>
<h3>Registered Successfully</h3>
<form:form action="" commandName="participant">
<table>
<tr><td><label>Participant Id:</label></td><td><form:input path="participant_Id"/></td></tr>
<tr><td><label>First Name:</label></td><td><form:input path="fName"/></td></tr>
<tr><td><label>Last Name:</label></td><td><form:input path="lName"/></td></tr>
<tr><td><label>Birth Date:</label></td><td><form:input path="birth_Date"/></td></tr>
<tr><td><label>Email:</label></td><td><form:input path="email"/></td></tr>

</table>
</form:form>
</body>
</html>