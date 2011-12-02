<%@ page language="java" contentType="text/html; charset=ISO-8859-1"
    pageEncoding="ISO-8859-1"%>
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=ISO-8859-1">
<title>Wockets-Data Check Action</title>
<style type="text/css">
input.btn { 
	  color:#050; 
	  font: bold 84% 'trebuchet ms',helvetica,sans-serif;
	  height: 40px;width:95%;
	}
textarea{
	overflow: scroll;
	overflow-y: scroll;
	overflow-x: hidden;
	overflow:-moz-scrollbars-vertical;
}	

</style>
</head>
<body bgcolor="#E6F4F7">
<h5 style="margin-bottom: 1px;">Participant ${pId}: Something's Wrong</h5>
<label>Note:</label><br/>
<textarea rows="6" cols="30" id="note" name="note">Write note.</textarea>
<br/>
<label>Take Action:</label>
<div style="height: 330px;width: 95%;border: 1px solid black;">
	<center>
		<div style="height: 180px;width: 97%;border: 1px solid black;margin-top: 4px;">
			<input type="button" value="  App Update  "/><input type="button" value="  App Restart  "/>
			<br/><br/>
			<textarea rows="6" cols="27" id="pSMSEmail" name="pSMSEmail">Send SMS/Email to participant.</textarea>
			<input type="button" value="   Send SMS   "/><input type="button" value="  Send Email  "/>
		</div>

		<div style="height: 135px;width: 97%;border: 1px solid black;margin-top: 4px;">
			<textarea rows="6" cols="27" id="teamSMSEmail" name="teamSMSEmail">Send email to research team.</textarea>
			<input type="button" value="Send Email To Research Team"/>
		</div>
</center>
<br/>
<label>Recheck data in:</label>
<select>
	<option value="">--Select--</option>
	<option value="12hr">12 hours</option>
	<option value="24hr">24 hours</option>
	<option value="2day">2 days</option>
	<option value="5day">5 days</option>
	<option value="7day">1 week</option>
</select>
<br/><br/>
<center>
<input type="button" class="btn" value="Finish Reviewing
Verified"/></center>
</div>
</body>
</html>