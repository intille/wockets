<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
<meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1" />
<title>Untitled Document</title>
</head>


<body>

<?php
$to      = 'albinali@mit.edu';
$subject = 'the subject';
$message = 'hello';
$headers = 'From: wockets@dhcp-18-85-23-131.mit.edu' . "\r\n" .
    'Reply-To: wockets@dhcp-18-85-23-131.media.mit.edu' . "\r\n" .
    'X-Mailer: PHP/' . phpversion();

$re=mail($to, $subject, $message, $headers);

if ($re)
	print "true";
else
	print "false";
?>


</body>
</html>
