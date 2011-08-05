<?php require_once('Connections/Wockets.php'); ?>
<?php
// Load the common classes
require_once('includes/common/KT_common.php');

// Load the tNG classes
require_once('includes/tng/tNG.inc.php');

// Load the KT_back class
require_once('includes/nxt/KT_back.php');

// Make a transaction dispatcher instance
$tNGs = new tNG_dispatcher("");

// Make unified connection variable
$conn_Wockets = new KT_connection($Wockets, $database_Wockets);

//start Trigger_CheckPasswords trigger
//remove this line if you want to edit the code by hand
function Trigger_CheckPasswords(&$tNG) {
  $myThrowError = new tNG_ThrowError($tNG);
  $myThrowError->setErrorMsg("Could not create account.");
  $myThrowError->setField("password");
  $myThrowError->setFieldErrorMsg("The two passwords do not match.");
  return $myThrowError->Execute();
}
//end Trigger_CheckPasswords trigger

// Start trigger
$formValidation = new tNG_FormValidation();
$formValidation->addField("username", true, "text", "", "", "", "");
$formValidation->addField("email", true, "text", "email", "", "", "");
$formValidation->addField("password", true, "text", "", "", "", "");
$tNGs->prepareValidation($formValidation);
// End trigger

//start Trigger_CheckOldPassword trigger
//remove this line if you want to edit the code by hand
function Trigger_CheckOldPassword(&$tNG) {
  return Trigger_UpdatePassword_CheckOldPassword($tNG);
}
//end Trigger_CheckOldPassword trigger

// Make an insert transaction instance
$ins_ACCOUNTS = new tNG_multipleInsert($conn_Wockets);
$tNGs->addTransaction($ins_ACCOUNTS);
// Register triggers
$ins_ACCOUNTS->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Insert1");
$ins_ACCOUNTS->registerTrigger("BEFORE", "Trigger_Default_FormValidation", 10, $formValidation);
$ins_ACCOUNTS->registerTrigger("END", "Trigger_Default_Redirect", 99, "includes/nxt/back.php");
$ins_ACCOUNTS->registerConditionalTrigger("{POST.password} != {POST.re_password}", "BEFORE", "Trigger_CheckPasswords", 50);
// Add columns
$ins_ACCOUNTS->setTable("ACCOUNTS");
$ins_ACCOUNTS->addColumn("username", "STRING_TYPE", "POST", "username");
$ins_ACCOUNTS->addColumn("first_name", "STRING_TYPE", "POST", "first_name");
$ins_ACCOUNTS->addColumn("last_name", "STRING_TYPE", "POST", "last_name");
$ins_ACCOUNTS->addColumn("email", "STRING_TYPE", "POST", "email");
$ins_ACCOUNTS->addColumn("password", "STRING_TYPE", "POST", "password");
$ins_ACCOUNTS->setPrimaryKey("user_id", "NUMERIC_TYPE");

// Make an update transaction instance
$upd_ACCOUNTS = new tNG_multipleUpdate($conn_Wockets);
$tNGs->addTransaction($upd_ACCOUNTS);
// Register triggers
$upd_ACCOUNTS->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Update1");
$upd_ACCOUNTS->registerTrigger("BEFORE", "Trigger_Default_FormValidation", 10, $formValidation);
$upd_ACCOUNTS->registerTrigger("END", "Trigger_Default_Redirect", 99, "includes/nxt/back.php");
$upd_ACCOUNTS->registerConditionalTrigger("{POST.password} != {POST.re_password}", "BEFORE", "Trigger_CheckPasswords", 50);
$upd_ACCOUNTS->registerTrigger("BEFORE", "Trigger_CheckOldPassword", 60);
// Add columns
$upd_ACCOUNTS->setTable("ACCOUNTS");
$upd_ACCOUNTS->addColumn("username", "STRING_TYPE", "POST", "username");
$upd_ACCOUNTS->addColumn("first_name", "STRING_TYPE", "POST", "first_name");
$upd_ACCOUNTS->addColumn("last_name", "STRING_TYPE", "POST", "last_name");
$upd_ACCOUNTS->addColumn("email", "STRING_TYPE", "POST", "email");
$upd_ACCOUNTS->addColumn("password", "STRING_TYPE", "POST", "password");
$upd_ACCOUNTS->setPrimaryKey("user_id", "NUMERIC_TYPE", "GET", "user_id");

// Make an instance of the transaction object
$del_ACCOUNTS = new tNG_multipleDelete($conn_Wockets);
$tNGs->addTransaction($del_ACCOUNTS);
// Register triggers
$del_ACCOUNTS->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Delete1");
$del_ACCOUNTS->registerTrigger("END", "Trigger_Default_Redirect", 99, "includes/nxt/back.php");
// Add columns
$del_ACCOUNTS->setTable("ACCOUNTS");
$del_ACCOUNTS->setPrimaryKey("user_id", "NUMERIC_TYPE", "GET", "user_id");

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
<script src="includes/nxt/scripts/form.js" type="text/javascript"></script>
<script src="includes/nxt/scripts/form.js.php" type="text/javascript"></script>
<script type="text/javascript">
$NXT_FORM_SETTINGS = {
  duplicate_buttons: true,
  show_as_grid: true,
  merge_down_value: true
}
</script>
</head>

<body>
<?php
	echo $tNGs->getErrorMsg();
?>
<div class="KT_tng">
  <h1>
    <?php 
// Show IF Conditional region1 
if (@$_GET['user_id'] == "") {
?>
      <?php echo NXT_getResource("Insert_FH"); ?>
      <?php 
// else Conditional region1
} else { ?>
      <?php echo NXT_getResource("Update_FH"); ?>
      <?php } 
// endif Conditional region1
?>
    ACCOUNTS </h1>
  <div class="KT_tngform">
    <form method="post" id="form1" action="<?php echo KT_escapeAttribute(KT_getFullUri()); ?>">
      <?php $cnt1 = 0; ?>
      <?php do { ?>
        <?php $cnt1++; ?>
        <?php 
// Show IF Conditional region1 
if (@$totalRows_rsACCOUNTS > 1) {
?>
          <h2><?php echo NXT_getResource("Record_FH"); ?> <?php echo $cnt1; ?></h2>
          <?php } 
// endif Conditional region1
?>
        <table cellpadding="2" cellspacing="0" class="KT_tngtable">
          <tr>
            <td class="KT_th"><label for="username_<?php echo $cnt1; ?>">Username:</label></td>
            <td><input type="text" name="username_<?php echo $cnt1; ?>" id="username_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsACCOUNTS['username']); ?>" size="32" maxlength="100" />
                <?php echo $tNGs->displayFieldHint("username");?> <?php echo $tNGs->displayFieldError("ACCOUNTS", "username", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="first_name_<?php echo $cnt1; ?>">First_name:</label></td>
            <td><input type="text" name="first_name_<?php echo $cnt1; ?>" id="first_name_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsACCOUNTS['first_name']); ?>" size="32" maxlength="100" />
                <?php echo $tNGs->displayFieldHint("first_name");?> <?php echo $tNGs->displayFieldError("ACCOUNTS", "first_name", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="last_name_<?php echo $cnt1; ?>">Last_name:</label></td>
            <td><input type="text" name="last_name_<?php echo $cnt1; ?>" id="last_name_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsACCOUNTS['last_name']); ?>" size="32" maxlength="100" />
                <?php echo $tNGs->displayFieldHint("last_name");?> <?php echo $tNGs->displayFieldError("ACCOUNTS", "last_name", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="email_<?php echo $cnt1; ?>">Email:</label></td>
            <td><input type="text" name="email_<?php echo $cnt1; ?>" id="email_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsACCOUNTS['email']); ?>" size="32" maxlength="100" />
                <?php echo $tNGs->displayFieldHint("email");?> <?php echo $tNGs->displayFieldError("ACCOUNTS", "email", $cnt1); ?> </td>
          </tr>
          <?php 
// Show IF Conditional show_old_password_on_update_only 
if (@$_GET['user_id'] != "") {
?>
            <tr>
              <td class="KT_th"><label for="old_password_<?php echo $cnt1; ?>">Old Password:</label></td>
              <td><input type="password" name="old_password_<?php echo $cnt1; ?>" id="old_password_<?php echo $cnt1; ?>" value="" size="32" maxlength="100" />
                  <?php echo $tNGs->displayFieldError("ACCOUNTS", "old_password", $cnt1); ?> </td>
            </tr>
            <?php } 
// endif Conditional show_old_password_on_update_only
?>
          <tr>
            <td class="KT_th"><label for="password_<?php echo $cnt1; ?>">Password:</label></td>
            <td><input type="password" name="password_<?php echo $cnt1; ?>" id="password_<?php echo $cnt1; ?>" value="" size="32" maxlength="100" />
                <?php echo $tNGs->displayFieldHint("password");?> <?php echo $tNGs->displayFieldError("ACCOUNTS", "password", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="re_password_<?php echo $cnt1; ?>">Re-type Password:</label></td>
            <td><input type="password" name="re_password_<?php echo $cnt1; ?>" id="re_password_<?php echo $cnt1; ?>" value="" size="32" maxlength="100" />
            </td>
          </tr>
        </table>
        <input type="hidden" name="kt_pk_ACCOUNTS_<?php echo $cnt1; ?>" class="id_field" value="<?php echo KT_escapeAttribute($row_rsACCOUNTS['kt_pk_ACCOUNTS']); ?>" />
        <?php } while ($row_rsACCOUNTS = mysql_fetch_assoc($rsACCOUNTS)); ?>
      <div class="KT_bottombuttons">
        <div>
          <?php 
      // Show IF Conditional region1
      if (@$_GET['user_id'] == "") {
      ?>
            <input type="submit" name="KT_Insert1" id="KT_Insert1" value="<?php echo NXT_getResource("Insert_FB"); ?>" />
            <?php 
      // else Conditional region1
      } else { ?>
            <div class="KT_operations">
              <input type="submit" name="KT_Insert1" value="<?php echo NXT_getResource("Insert as new_FB"); ?>" onclick="nxt_form_insertasnew(this, 'user_id')" />
            </div>
            <input type="submit" name="KT_Update1" value="<?php echo NXT_getResource("Update_FB"); ?>" />
            <input type="submit" name="KT_Delete1" value="<?php echo NXT_getResource("Delete_FB"); ?>" onclick="return confirm('<?php echo NXT_getResource("Are you sure?"); ?>');" />
            <?php }
      // endif Conditional region1
      ?>
          <input type="button" name="KT_Cancel1" value="<?php echo NXT_getResource("Cancel_FB"); ?>" onclick="return UNI_navigateCancel(event, 'includes/nxt/back.php')" />
        </div>
      </div>
    </form>
  </div>
  <br class="clearfixplain" />
</div>
<p>&nbsp;</p>
</body>
</html>
