<%@ page language="java" contentType="text/html; charset=ISO-8859-1"
    pageEncoding="ISO-8859-1"%>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=ISO-8859-1">
<title>Wocket - Account Recovery</title>
<script type="text/javascript">
function submit()
{
	var email = document.getElementById("email").value;
	if(email != "")
	{
		var xmlhttp = getAjaxGETRequest();
		xmlhttp.onreadystatechange=function(){
		  if (xmlhttp.readyState==4 && xmlhttp.status==200)
		  {
		    var result=xmlhttp.responseText;
		    if(result =="true")
		    	alert("Account credential has been sent to entered email address.");
		    else
		    	alert("Email address not found in wocket record, please enter correct email address");
		   }
		 };
		  xmlhttp.open("GET","recoverAccount.html?email="+email,true);
		  xmlhttp.send();
	}
	else
		alert("Please enter valid email address before submit.")
}

</script>
</head>
<body>
<h2>Wocket Account</h2>
<b>Forgot Your Account Detail?</b><br/>
<p>To get your wocket account credential type your full email address which you entered during account creation.</p>
<b>Email Address</b><br/>
<input type="text" id="email" name="email"/>
<br/><br/>
<input type="button" value="Submit" onclick="submit()"/>
<br/><br/><br/><br/><br/><br/><br/><br/><br/>
<br/><br/><br/><br/><br/><br/><br/><br/><br/>
<br/><br/><br/><br/><br/><br/><br/><br/><br/>
</body>
</html>