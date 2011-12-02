<%@ page language="java" contentType="text/html; charset=ISO-8859-1"
    pageEncoding="ISO-8859-1"%>
    <%@taglib prefix="c" uri="http://java.sun.com/jsp/jstl/core" %>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=ISO-8859-1">
<title>Wockets - Login</title>
<style type="text/css">
.bluebold {
font: bold italic 20px Georgia, "Times New Roman", Times, serif; color:#00478a;
}
</style>
</head>
<body>
<br/><br/><br/><br/><br/><br/><br/><br/>
<center>
 <div class="bluebold">
 &nbsp;&nbsp;&nbsp;&nbsp;
&nbsp;&nbsp;
 Login Information</div>
 <br/>
    <form action="loginSubmit.html" method="post">
    <c:if test="${err!=null}"><label style="color:red;">&nbsp;&nbsp;&nbsp;&nbsp;${err}</label></c:if>
    <table>
    <tr>
    <td><label>User Name:</label></td><td><input type="text" name="userName" maxlength="100"/></td>
    </tr>
    <tr>
    <td><label>Password:</label><td><input type="password" name="pwd" maxlength="100"/></td>
    </tr>
    <tr>
    <td></td><td><input type="submit" value="Sign in"/></td>
    </tr>
    </table>
    </form>
    <a href="accountRecovery.html">Can't access your account?</a>
    </center>
<br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/>
</body>
</html>