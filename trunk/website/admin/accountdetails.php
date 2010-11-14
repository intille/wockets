<?php require_once('../Connections/Wockets.php'); ?>
<?php
// Load the common classes
require_once('../includes/common/KT_common.php');

// Load the tNG classes
require_once('../includes/tng/tNG.inc.php');

// Load the KT_back class
require_once('../includes/nxt/KT_back.php');

// Make a transaction dispatcher instance
$tNGs = new tNG_dispatcher("../");

// Make unified connection variable
$conn_Wockets = new KT_connection($Wockets, $database_Wockets);

// Start trigger
$formValidation = new tNG_FormValidation();
$formValidation->addField("username", true, "text", "", "4", "", "Your username should have at least 4 characters.");
$formValidation->addField("password", true, "text", "", "8", "", "Your password should have at least 8 characters.");
$formValidation->addField("first_name", true, "text", "", "", "", "");
$formValidation->addField("last_name", true, "text", "", "", "", "");
$formValidation->addField("email", true, "text", "email", "", "", "Please enter a valid email address.");
$formValidation->addField("registration_datetime", true, "date", "", "", "", "");
$tNGs->prepareValidation($formValidation);
// End trigger

// Make an insert transaction instance
$ins_ACCOUNTS = new tNG_multipleInsert($conn_Wockets);
$tNGs->addTransaction($ins_ACCOUNTS);
// Register triggers
$ins_ACCOUNTS->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Insert1");
$ins_ACCOUNTS->registerTrigger("BEFORE", "Trigger_Default_FormValidation", 10, $formValidation);
$ins_ACCOUNTS->registerTrigger("END", "Trigger_Default_Redirect", 99, "../includes/nxt/back.php");
// Add columns
$ins_ACCOUNTS->setTable("ACCOUNTS");
$ins_ACCOUNTS->addColumn("user_id", "NUMERIC_TYPE", "POST", "user_id");
$ins_ACCOUNTS->addColumn("username", "STRING_TYPE", "POST", "username");
$ins_ACCOUNTS->addColumn("password", "STRING_TYPE", "POST", "password");
$ins_ACCOUNTS->addColumn("first_name", "STRING_TYPE", "POST", "first_name");
$ins_ACCOUNTS->addColumn("last_name", "STRING_TYPE", "POST", "last_name");
$ins_ACCOUNTS->addColumn("email", "STRING_TYPE", "POST", "email");
$ins_ACCOUNTS->addColumn("registration_datetime", "DATE_TYPE", "POST", "registration_datetime");
$ins_ACCOUNTS->addColumn("active", "CHECKBOX_1_0_TYPE", "POST", "active", "0");
$ins_ACCOUNTS->addColumn("user_type", "STRING_TYPE", "POST", "user_type");
$ins_ACCOUNTS->addColumn("disable_date", "DATE_TYPE", "POST", "disable_date");
$ins_ACCOUNTS->addColumn("attempts", "STRING_TYPE", "POST", "attempts");
$ins_ACCOUNTS->setPrimaryKey("user_id", "NUMERIC_TYPE");

// Make an update transaction instance
$upd_ACCOUNTS = new tNG_multipleUpdate($conn_Wockets);
$tNGs->addTransaction($upd_ACCOUNTS);
// Register triggers
$upd_ACCOUNTS->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Update1");
$upd_ACCOUNTS->registerTrigger("BEFORE", "Trigger_Default_FormValidation", 10, $formValidation);
$upd_ACCOUNTS->registerTrigger("END", "Trigger_Default_Redirect", 99, "../includes/nxt/back.php");
// Add columns
$upd_ACCOUNTS->setTable("ACCOUNTS");
$upd_ACCOUNTS->addColumn("user_id", "NUMERIC_TYPE", "POST", "user_id");
$upd_ACCOUNTS->addColumn("username", "STRING_TYPE", "POST", "username");
$upd_ACCOUNTS->addColumn("password", "STRING_TYPE", "POST", "password");
$upd_ACCOUNTS->addColumn("first_name", "STRING_TYPE", "POST", "first_name");
$upd_ACCOUNTS->addColumn("last_name", "STRING_TYPE", "POST", "last_name");
$upd_ACCOUNTS->addColumn("email", "STRING_TYPE", "POST", "email");
$upd_ACCOUNTS->addColumn("registration_datetime", "DATE_TYPE", "POST", "registration_datetime");
$upd_ACCOUNTS->addColumn("active", "CHECKBOX_1_0_TYPE", "POST", "active");
$upd_ACCOUNTS->addColumn("user_type", "STRING_TYPE", "POST", "user_type");
$upd_ACCOUNTS->addColumn("disable_date", "DATE_TYPE", "POST", "disable_date");
$upd_ACCOUNTS->addColumn("attempts", "STRING_TYPE", "POST", "attempts");
$upd_ACCOUNTS->setPrimaryKey("user_id", "NUMERIC_TYPE", "GET", "user_id");

// Make an instance of the transaction object
$del_ACCOUNTS = new tNG_multipleDelete($conn_Wockets);
$tNGs->addTransaction($del_ACCOUNTS);
// Register triggers
$del_ACCOUNTS->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Delete1");
$del_ACCOUNTS->registerTrigger("END", "Trigger_Default_Redirect", 99, "../includes/nxt/back.php");
// Add columns
$del_ACCOUNTS->setTable("ACCOUNTS");
$del_ACCOUNTS->setPrimaryKey("user_id", "NUMERIC_TYPE", "GET", "user_id");

// Execute all the registered transactions
$tNGs->executeTransactions();

// Get the transaction recordset
$rsACCOUNTS = $tNGs->getRecordset("ACCOUNTS");
$row_rsACCOUNTS = mysql_fetch_assoc($rsACCOUNTS);
$totalRows_rsACCOUNTS = mysql_num_rows($rsACCOUNTS);
?><!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
<meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1" />
<title>Untitled Document</title>
<link href="../includes/skins/mxkollection3.css" rel="stylesheet" type="text/css" media="all" />
<script src="../includes/common/js/base.js" type="text/javascript"></script>
<script src="../includes/common/js/utility.js" type="text/javascript"></script>
<script src="../includes/skins/style.js" type="text/javascript"></script>
<?php echo $tNGs->displayValidationRules();?>
<script src="../includes/nxt/scripts/form.js" type="text/javascript"></script>
<script src="../includes/nxt/scripts/form.js.php" type="text/javascript"></script>
<script type="text/javascript">
$NXT_FORM_SETTINGS = {
  duplicate_buttons: true,
  show_as_grid: true,
  merge_down_value: true
}
</script>
</head>

<body>
<a href="index.php">Admin Home</a>
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
            <td class="KT_th"><label for="user_id_<?php echo $cnt1; ?>">User ID:</label></td>
            <td><input type="text" name="user_id_<?php echo $cnt1; ?>" id="user_id_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsACCOUNTS['user_id']); ?>" size="7" />
                <?php echo $tNGs->displayFieldHint("user_id");?> <?php echo $tNGs->displayFieldError("ACCOUNTS", "user_id", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="username_<?php echo $cnt1; ?>">Username:</label></td>
            <td><input type="text" name="username_<?php echo $cnt1; ?>" id="username_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsACCOUNTS['username']); ?>" size="32" maxlength="100" />
                <?php echo $tNGs->displayFieldHint("username");?> <?php echo $tNGs->displayFieldError("ACCOUNTS", "username", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="password_<?php echo $cnt1; ?>">Password:</label></td>
            <td><input type="text" name="password_<?php echo $cnt1; ?>" id="password_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsACCOUNTS['password']); ?>" size="32" maxlength="100" />
                <?php echo $tNGs->displayFieldHint("password");?> <?php echo $tNGs->displayFieldError("ACCOUNTS", "password", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="first_name_<?php echo $cnt1; ?>">First Name:</label></td>
            <td><input type="text" name="first_name_<?php echo $cnt1; ?>" id="first_name_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsACCOUNTS['first_name']); ?>" size="32" maxlength="100" />
                <?php echo $tNGs->displayFieldHint("first_name");?> <?php echo $tNGs->displayFieldError("ACCOUNTS", "first_name", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="last_name_<?php echo $cnt1; ?>">Last Name:</label></td>
            <td><input type="text" name="last_name_<?php echo $cnt1; ?>" id="last_name_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsACCOUNTS['last_name']); ?>" size="32" maxlength="100" />
                <?php echo $tNGs->displayFieldHint("last_name");?> <?php echo $tNGs->displayFieldError("ACCOUNTS", "last_name", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="email_<?php echo $cnt1; ?>">Email:</label></td>
            <td><input type="text" name="email_<?php echo $cnt1; ?>" id="email_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsACCOUNTS['email']); ?>" size="32" maxlength="100" />
                <?php echo $tNGs->displayFieldHint("email");?> <?php echo $tNGs->displayFieldError("ACCOUNTS", "email", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="registration_datetime_<?php echo $cnt1; ?>">Registration Date:</label></td>
            <td><input type="text" name="registration_datetime_<?php echo $cnt1; ?>" id="registration_datetime_<?php echo $cnt1; ?>" value="<?php echo KT_formatDate($row_rsACCOUNTS['registration_datetime']); ?>" size="10" maxlength="22" />
                <?php echo $tNGs->displayFieldHint("registration_datetime");?> <?php echo $tNGs->displayFieldError("ACCOUNTS", "registration_datetime", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="active_<?php echo $cnt1; ?>">Active:</label></td>
            <td><input  <?php if (!(strcmp(KT_escapeAttribute($row_rsACCOUNTS['active']),"1"))) {echo "checked";} ?> type="checkbox" name="active_<?php echo $cnt1; ?>" id="active_<?php echo $cnt1; ?>" value="1" />
                <?php echo $tNGs->displayFieldError("ACCOUNTS", "active", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="user_type_<?php echo $cnt1; ?>">User_type:</label></td>
            <td><select name="user_type_<?php echo $cnt1; ?>" id="user_type_<?php echo $cnt1; ?>">
              <option value="regular" <?php if (!(strcmp("regular", KT_escapeAttribute($row_rsACCOUNTS['user_type'])))) {echo "SELECTED";} ?>>regular</option>
              <option value="admin" <?php if (!(strcmp("admin", KT_escapeAttribute($row_rsACCOUNTS['user_type'])))) {echo "SELECTED";} ?>>admin</option>
            </select>
                <?php echo $tNGs->displayFieldError("ACCOUNTS", "user_type", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="disable_date_<?php echo $cnt1; ?>">Disable Date</label></td>
            <td><input type="text" name="disable_date_<?php echo $cnt1; ?>" id="disable_date_<?php echo $cnt1; ?>" value="<?php echo KT_formatDate($row_rsACCOUNTS['disable_date']); ?>" size="10" maxlength="22" />
                <?php echo $tNGs->displayFieldHint("disable_date");?> <?php echo $tNGs->displayFieldError("ACCOUNTS", "disable_date", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="attempts_<?php echo $cnt1; ?>">Failed Login Attempts:</label></td>
            <td><input type="text" name="attempts_<?php echo $cnt1; ?>" id="attempts_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsACCOUNTS['attempts']); ?>" size="16" maxlength="16" />
                <?php echo $tNGs->displayFieldHint("attempts");?> <?php echo $tNGs->displayFieldError("ACCOUNTS", "attempts", $cnt1); ?> </td>
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
          <input type="button" name="KT_Cancel1" value="<?php echo NXT_getResource("Cancel_FB"); ?>" onclick="return UNI_navigateCancel(event, '../includes/nxt/back.php')" />
        </div>
      </div>
    </form>
  </div>
  <br class="clearfixplain" />
</div>
<p>&nbsp;</p>
</body>
</html>
