<?php if ($_POST['username']){
  require_once('recaptchalib.php');
  $privatekey = "6Ldzx7wSAAAAAIXj9XX5QoxK0zKvfuIQyFrtuaPP";
  $resp = recaptcha_check_answer ($privatekey,
                                $_SERVER["REMOTE_ADDR"],
                                $_POST["recaptcha_challenge_field"],
                                $_POST["recaptcha_response_field"]);
  if (!$resp->is_valid) {
    $host  = $_SERVER['HTTP_HOST'];
	$uri   = rtrim(dirname($_SERVER['PHP_SELF']), '/\\');
	$extra = 'register.php?status=failure';
	header("Location: http://$host$uri/$extra");
	exit; 
  } else {
    // do nothing
  }
  }?>
<?php require_once('Connections/Wockets.php'); ?>
<?php
// Load the common classes
require_once('includes/common/KT_common.php');

// Load the tNG classes
require_once('includes/tng/tNG.inc.php');

// Make a transaction dispatcher instance
$tNGs = new tNG_dispatcher("");

// Make unified connection variable
$conn_Wockets = new KT_connection($Wockets, $database_Wockets);

//start Trigger_CheckPasswords trigger
//remove this line if you want to edit the code by hand
function Trigger_CheckPasswords(&$tNG) {
  $myThrowError = new tNG_ThrowError($tNG);
  $myThrowError->setErrorMsg("Passwords do not match.");
  $myThrowError->setField("password");
  $myThrowError->setFieldErrorMsg("The two passwords do not match.");
  return $myThrowError->Execute();
}
//end Trigger_CheckPasswords trigger

//start Trigger_WelcomeEmail trigger
//remove this line if you want to edit the code by hand
function Trigger_WelcomeEmail(&$tNG) {
  $emailObj = new tNG_Email($tNG);
  $emailObj->setFrom("{KT_defaultSender}");
  $emailObj->setTo("{email}");
  $emailObj->setCC("");
  $emailObj->setBCC("");
  $emailObj->setSubject("Welcome");
  //FromFile method
  $emailObj->setContentFile("includes/mailtemplates/welcome.html");
  $emailObj->setEncoding("ISO-8859-1");
  $emailObj->setFormat("HTML/Text");
  $emailObj->setImportance("Normal");
  return $emailObj->Execute();
}
//end Trigger_WelcomeEmail trigger

//start Trigger_ActivationEmail trigger
//remove this line if you want to edit the code by hand
function Trigger_ActivationEmail(&$tNG) {
  $emailObj = new tNG_Email($tNG);
  $emailObj->setFrom("{KT_defaultSender}");
  $emailObj->setTo("{email}");
  $emailObj->setCC("");
  $emailObj->setBCC("");
  $emailObj->setSubject("Activation");
  //FromFile method
  $emailObj->setContentFile("includes/mailtemplates/activate.html");
  $emailObj->setEncoding("ISO-8859-1");
  $emailObj->setFormat("HTML/Text");
  $emailObj->setImportance("Normal");
  return $emailObj->Execute();
}
//end Trigger_ActivationEmail trigger

// Start trigger
$formValidation = new tNG_FormValidation();
$formValidation->addField("username", true, "text", "", "4", "", "Your username should have at least 4 characters.");
$formValidation->addField("first_name", true, "text", "", "", "", "");
$formValidation->addField("password", true, "text", "", "8", "", "Your password should have at least 8 characters.");
$formValidation->addField("last_name", true, "text", "", "", "", "");
$formValidation->addField("email", true, "text", "email", "", "", "Please enter a valid email address.");
$formValidation->addField("registration_datetime", true, "date", "", "", "", "");
$tNGs->prepareValidation($formValidation);
// End trigger

// Make an insert transaction instance
$userRegistration = new tNG_insert($conn_Wockets);
$tNGs->addTransaction($userRegistration);
// Register triggers
$userRegistration->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Insert1");
$userRegistration->registerTrigger("BEFORE", "Trigger_Default_FormValidation", 10, $formValidation);
$userRegistration->registerTrigger("END", "Trigger_Default_Redirect", 99, "{kt_login_redirect}");
$userRegistration->registerConditionalTrigger("{POST.password} != {POST.re_password}", "BEFORE", "Trigger_CheckPasswords", 50);
$userRegistration->registerTrigger("AFTER", "Trigger_WelcomeEmail", 40);
$userRegistration->registerTrigger("AFTER", "Trigger_ActivationEmail", 40);
// Add columns
$userRegistration->setTable("ACCOUNTS");
$userRegistration->addColumn("username", "STRING_TYPE", "POST", "username");
$userRegistration->addColumn("first_name", "STRING_TYPE", "POST", "first_name");
$userRegistration->addColumn("password", "STRING_TYPE", "POST", "password");
$userRegistration->addColumn("last_name", "STRING_TYPE", "POST", "last_name");
$userRegistration->addColumn("email", "STRING_TYPE", "POST", "email");
$userRegistration->addColumn("registration_datetime", "STRING_TYPE", "POST", "registration_datetime");
$userRegistration->setPrimaryKey("user_id", "NUMERIC_TYPE");

// Execute all the registered transactions
$tNGs->executeTransactions();

// Get the transaction recordset
$rsACCOUNTS = $tNGs->getRecordset("ACCOUNTS");
$row_rsACCOUNTS = mysql_fetch_assoc($rsACCOUNTS);
$totalRows_rsACCOUNTS = mysql_num_rows($rsACCOUNTS);
?>
<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
<meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1" />
<title>Untitled Document</title>
<link href="includes/skins/mxkollection3.css" rel="stylesheet" type="text/css" media="all" />
<script src="includes/common/js/base.js" type="text/javascript"></script>
<script src="includes/common/js/utility.js" type="text/javascript"></script>
<script src="includes/skins/style.js" type="text/javascript"></script>
<?php echo $tNGs->displayValidationRules();?>
<style type="text/css">
<!--
.style1 {font-size: x-large}
-->
</style>
</head>

<body>
<p class="style1">
<img src="images/logo.png" alt="Wockets" width="128" height="136" />New Member Registration</p>
<?php
	echo $tNGs->getErrorMsg();
?>
<form method="post" id="form1" action="<?php echo KT_escapeAttribute(KT_getFullUri()); ?>">
  <table cellpadding="2" cellspacing="0" class="KT_tngtable">
    <tr>
      <td class="KT_th"><label for="username">Username:</label></td>
      <td><input type="text" name="username" id="username" value="<?php echo KT_escapeAttribute($row_rsACCOUNTS['username']); ?>" size="32" />
          <?php echo $tNGs->displayFieldHint("username");?> <?php echo $tNGs->displayFieldError("ACCOUNTS", "username"); ?> </td>
    </tr>
        <tr>
      <td class="KT_th"><label for="password">Password:</label></td>
      <td><input type="password" name="password" id="password" value="" size="32" />
          <?php echo $tNGs->displayFieldHint("password");?> <?php echo $tNGs->displayFieldError("ACCOUNTS", "password"); ?> </td>
    </tr>
    <tr>
      <td class="KT_th"><label for="re_password">Re-type Password:</label></td>
      <td><input type="password" name="re_password" id="re_password" value="" size="32" />
      </td>
    </tr>
	<tr>
      <td class="KT_th"><label for="first_name">First Name:</label></td>
      <td><input type="text" name="first_name" id="first_name" value="<?php echo KT_escapeAttribute($row_rsACCOUNTS['first_name']); ?>" size="32" />
          <?php echo $tNGs->displayFieldHint("first_name");?> <?php echo $tNGs->displayFieldError("ACCOUNTS", "first_name"); ?> </td>
    </tr>
    <tr>
      <td class="KT_th"><label for="last_name">Last Name:</label></td>
      <td><input type="text" name="last_name" id="last_name" value="<?php echo KT_escapeAttribute($row_rsACCOUNTS['last_name']); ?>" size="32" />
          <?php echo $tNGs->displayFieldHint("last_name");?> <?php echo $tNGs->displayFieldError("ACCOUNTS", "last_name"); ?> </td>
    </tr>
    <tr>
      <td class="KT_th"><label for="email">Email:</label></td>
      <td><input type="text" name="email" id="email" value="<?php echo KT_escapeAttribute($row_rsACCOUNTS['email']); ?>" size="32" />
          <?php echo $tNGs->displayFieldHint("email");?> <?php echo $tNGs->displayFieldError("ACCOUNTS", "email"); ?> </td>
    </tr>
	<tr><td>
	<?php
	 require_once('recaptchalib.php');
  	 $publickey = "6Ldzx7wSAAAAAMX1fDdCa69BrxDeM9kZwvyUTHyB"; // you got this from the signup page
  	 echo recaptcha_get_html($publickey);
	?>
	</td></tr>
    <tr class="KT_buttons">
      <td colspan="2"><input type="submit" name="KT_Insert1" id="KT_Insert1" value="Register" />
      </td>
    </tr>
  </table>
  <input type="hidden" name="registration_datetime" id="registration_datetime" value="<?php  echo date("Y-m-d H:m:s");?>" />
</form>
<p>&nbsp;</p>
</body>
</html>
