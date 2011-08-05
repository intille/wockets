<?php require_once('../Connections/Wockets.php'); ?>
<?php
// Load the common classes
require_once('../includes/common/KT_common.php');
?><?php
// Load the tNG classes
require_once('../includes/tng/tNG.inc.php');
?><?php
// Make a transaction dispatcher instance
$tNGs = new tNG_dispatcher("../");
?><?php
// Make unified connection variable
$conn_Wockets = new KT_connection($Wockets, $database_Wockets);
?>
<?php
// Start trigger
$formValidation = new tNG_FormValidation();
$formValidation->addField("email", true, "text", "email", "", "", "");
$tNGs->prepareValidation($formValidation);
// End trigger
?>
<?php
//start Trigger_ForgotPasswordCheckEmail trigger
//remove this line if you want to edit the code by hand
function Trigger_ForgotPasswordCheckEmail(&$tNG) {
  return Trigger_ForgotPassword_CheckEmail($tNG);
}
//end Trigger_ForgotPasswordCheckEmail trigger
?>
<?php
//start Trigger_ForgotPassword_Email trigger
//remove this line if you want to edit the code by hand
function Trigger_ForgotPassword_Email(&$tNG) {
  $emailObj = new tNG_Email($tNG);
  $emailObj->setFrom("{KT_defaultSender}");
  $emailObj->setTo("{email}");
  $emailObj->setCC("");
  $emailObj->setBCC("");
  $emailObj->setSubject("Forgot password email");
  //FromFile method
  $emailObj->setContentFile("../includes/mailtemplates/forgot.html");
  $emailObj->setEncoding("ISO-8859-1");
  $emailObj->setFormat("HTML/Text");
  $emailObj->setImportance("Normal");
  return $emailObj->Execute();
}
//end Trigger_ForgotPassword_Email trigger
?>
<?php
// Make an update transaction instance
$forgotpass_transaction = new tNG_update($conn_Wockets);
$tNGs->addTransaction($forgotpass_transaction);
// Register triggers
$forgotpass_transaction->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Update1");
$forgotpass_transaction->registerTrigger("BEFORE", "Trigger_Default_FormValidation", 10, $formValidation);
$forgotpass_transaction->registerTrigger("BEFORE", "Trigger_ForgotPasswordCheckEmail", 20);
$forgotpass_transaction->registerTrigger("AFTER", "Trigger_ForgotPassword_Email", 1);
$forgotpass_transaction->registerTrigger("END", "Trigger_Default_Redirect", 99, "{kt_login_redirect}");
// Add columns
$forgotpass_transaction->setTable("ACCOUNTS");
$forgotpass_transaction->addColumn("email", "STRING_TYPE", "POST", "email");
$forgotpass_transaction->setPrimaryKey("email", "STRING_TYPE", "POST", "email");
?><?php
// Execute all the registered transactions
$tNGs->executeTransactions();
?><?php
// Get the transaction recordset
$rsACCOUNTS = $tNGs->getRecordset("ACCOUNTS");
$row_rsACCOUNTS = mysql_fetch_assoc($rsACCOUNTS);
$totalRows_rsACCOUNTS = mysql_num_rows($rsACCOUNTS);
?>
<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
<meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1">
<title>Forgot Password Page</title>
<link href="../includes/skins/mxkollection3.css" rel="stylesheet" type="text/css" media="all" /><script src="../includes/common/js/base.js" type="text/javascript"></script><script src="../includes/common/js/utility.js" type="text/javascript"></script><script src="../includes/skins/style.js" type="text/javascript"></script>
<?php echo $tNGs->displayValidationRules();?>
</head>

<body>

<?php
	echo $tNGs->getErrorMsg();
?>
	<form method="post" id="form1" action="<?php echo KT_escapeAttribute(KT_getFullUri()); ?>">
	<table cellpadding="2" cellspacing="0" class="KT_tngtable">
			
				
<tr>
	<td class="KT_th"><label for="email"> Email:</label></td>
	<td>
		<input type="text" name="email" id="email" value="<?php echo KT_escapeAttribute($row_rsACCOUNTS['email']); ?>" size="32" />
		<?php echo $tNGs->displayFieldHint("email");?>
		<?php echo $tNGs->displayFieldError("ACCOUNTS", "email"); ?>
	</td>
</tr>

			
			<tr class="KT_buttons"> 
				<td colspan="2">
					<input type="submit" name="KT_Update1" id="KT_Update1" value="Submit" />
				</td>
			</tr>      
		</table>
		    
	</form>
	<p>&nbsp;</p>

</body>
</html>
