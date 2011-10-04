<%@ page language="java" contentType="text/html; charset=ISO-8859-1"
    pageEncoding="ISO-8859-1"%>
    <%@taglib uri="http://www.springframework.org/tags/form" prefix="form"%>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=ISO-8859-1">
<title>Wockets - Personal Information</title>
<script type="text/javascript">
var fName=null;
var lName=null;
var email=null;

function afterPageLoad()
{
	fName = document.getElementById("fName").value;
	lName = document.getElementById("lName").value;
	email = document.getElementById("email").value;
}

function generatePwdUpdateDiv()
{
document.getElementById("passwordUpdate").style.display = "";
document.getElementById("newPwd").value="";
document.getElementById("oldPwd").value="";
document.getElementById("rePwd").value="";
}

function hidePwdUpdateDiv()
{
document.getElementById("passwordUpdate").style.display = "none";
}

function submitForm()
{
	if(document.getElementById("errorLabel"))
		document.getElementById("errorDiv").removeChild(document.getElementById("errorLabel"));
	var radioValue = getRadioValue();
	
	if(	document.getElementById("fName").value ==fName &&
		document.getElementById("lName").value ==lName &&
		document.getElementById("email").value ==email &&
		radioValue =="no")
		{
			return;
		}
	else
		{
		var errorMssg = formValidation();
		if(errorMssg !="")
			createErrorLabel(errorMssg,document.getElementById("errorDiv"));
		else
			{
				document.updatePersonalInfo.submit(); //submitform
			}

		}
}

function formValidation()
{
var errorMessage ="";
if(	document.getElementById("fName").value =="" ||
	document.getElementById("lName").value =="" ||
	document.getElementById("email").value =="")
	{
	errorMessage += "All fields are mendatory.<br/>";
	}

//check valid email Id
var x =document.getElementById("email").value;
var atpos =x.indexOf("@");
var dotpos =x.lastIndexOf(".");
if (atpos<1 || dotpos<atpos+2 || dotpos+2>=x.length)
  {
	errorMessage += "Not a valid email id.<br/>";
  }

var radioValue = getRadioValue();
if(radioValue =='yes') //password validation
{
//chacek new password
if(document.getElementById("newPwd").value != document.getElementById("rePwd").value)
	errorMessage += "New Password and Re- Password must be same.<br/>";

else if(document.getElementById("newPwd").value=="" || document.getElementById("rePwd").value =="")
	errorMessage += "New Password can not be blank.<br/>";
	
else
{
	if(document.getElementById("oldPwd").value =="")
		errorMessage += "Old password can not be blank.";
	else
	{
		var oldPwd = ajaxForOldPwdValidation(document.getElementById("oldPwd").value);
		if(oldPwd == "" || oldPwd != document.getElementById("pwd").value)
			errorMessage += "Old password did not match.";	
	}

}
}//close password validation if loop
return errorMessage;
}

function getRadioValue()
{
var radioButtons = document.getElementsByName("changePwd");
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

//send Ajax request to validate old password
function ajaxForOldPwdValidation(oldPwd)
{
var result = "";
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
		result = xmlHttp.responseText;
	}
}
xmlHttp.open("POST","oldPwdValidation.html",false);
xmlHttp.setRequestHeader("Content-type","application/x-www-form-urlencoded");
xmlHttp.send("oldPwd="+oldPwd);
return result;
}

</script>


</head>
<body>
<h4>Personal Information</h4>
<form:form action="updatePersonalInfo.html" method="POST" commandName="user" name="updatePersonalInfo">
<div id=errorDiv></div>
<table>
<tr>
<td><label>User Id:</label></td><td><form:input path="user_Id" readonly="true" style="background-color:#D9D9D9"/></td>
</tr>
<tr>
<td><label>First Name:</label></td><td><form:input path="fName" id="fName"/></td>
<td><label>Last Name:</label></td><td><form:input path="lName" id="lName"/></td>
</tr>
<tr>
<td><label>Email:</label></td><td><form:input path="email" id="email"/></td>
</tr>
</table>
<h4>Account Information</h4>

<td><label>Change Account Detail:</label><input type="radio" name="changePwd" value="yes" onclick="generatePwdUpdateDiv();"/>Yes
<input type="radio" name="changePwd" value="no" checked="checked" onclick="hidePwdUpdateDiv();"/>No</td>

<div id="passwordUpdate" style="display: none;">
<table>
<tr>
<td><label>User Name:</label></td><td><form:input path="Account.userName" readonly="true" style="background-color:#D9D9D9"/></td>
</tr>
<tr>
<td><label>User Type:</label></td><td><form:input path="Account.role" readonly="true" style="background-color:#D9D9D9"/></td>
</tr>
<tr>
<td><label>Old Password:</label></td><td><input type="password" name="oldPwd" id="oldPwd"/>
<form:hidden path="Account.pwd" id="pwd"/>
</td>
</tr>
<tr>
<td><label>New Password:</label></td><td><input type="password" name="newPwd" id="newPwd"/></td>
</tr>
<tr>
<td><label>Re-Password:</label></td><td><input type="password" name="rePwd" id="rePwd"/></td>
</tr>
</table>
</div>

<table>
<tr><td>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;</td>
<td><input type="button" value="   Update   " onclick="submitForm();"/></td></tr>
</table>
<script type="text/javascript">
window.onload=afterPageLoad();
</script>
</form:form>
<br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/><br/>
</body>
</html>