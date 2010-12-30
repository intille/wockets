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

//Start Restrict Access To Page
$restrict = new tNG_RestrictAccess($conn_Wockets, "../");
//Grand Levels: Any
$restrict->Execute();
//End Restrict Access To Page

// Start trigger
$formValidation = new tNG_FormValidation();
$formValidation->addField("first_name", true, "text", "", "", "", "");
$formValidation->addField("last_name", true, "text", "", "", "", "");
$formValidation->addField("email", true, "text", "", "", "", "");
$formValidation->addField("phonenumber", true, "text", "", "", "", "");
$formValidation->addField("birthyear", true, "numeric", "", "", "", "");
$formValidation->addField("gender", true, "text", "", "", "", "");
$formValidation->addField("start_date", false, "date", "datetime", "", "", "");
$formValidation->addField("end_date", false, "date", "datetime", "", "", "");
$tNGs->prepareValidation($formValidation);
// End trigger

// Make an insert transaction instance
$ins_PARTICIPANTS = new tNG_multipleInsert($conn_Wockets);
$tNGs->addTransaction($ins_PARTICIPANTS);
// Register triggers
$ins_PARTICIPANTS->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Insert1");
$ins_PARTICIPANTS->registerTrigger("BEFORE", "Trigger_Default_FormValidation", 10, $formValidation);
$ins_PARTICIPANTS->registerTrigger("END", "Trigger_Default_Redirect", 99, "../includes/nxt/back.php");
// Add columns
$ins_PARTICIPANTS->setTable("PARTICIPANTS");
$ins_PARTICIPANTS->addColumn("first_name", "STRING_TYPE", "POST", "first_name");
$ins_PARTICIPANTS->addColumn("last_name", "STRING_TYPE", "POST", "last_name");
$ins_PARTICIPANTS->addColumn("email", "STRING_TYPE", "POST", "email");
$ins_PARTICIPANTS->addColumn("phonenumber", "STRING_TYPE", "POST", "phonenumber");
$ins_PARTICIPANTS->addColumn("birthyear", "NUMERIC_TYPE", "POST", "birthyear");
$ins_PARTICIPANTS->addColumn("gender", "STRING_TYPE", "POST", "gender");
$ins_PARTICIPANTS->addColumn("height", "NUMERIC_TYPE", "POST", "height");
$ins_PARTICIPANTS->addColumn("weight", "NUMERIC_TYPE", "POST", "weight");
$ins_PARTICIPANTS->addColumn("race", "STRING_TYPE", "POST", "race");
$ins_PARTICIPANTS->addColumn("start_date", "DATE_TYPE", "POST", "start_date");
$ins_PARTICIPANTS->addColumn("end_date", "DATE_TYPE", "POST", "end_date");
$ins_PARTICIPANTS->addColumn("notes", "STRING_TYPE", "POST", "notes");
$ins_PARTICIPANTS->setPrimaryKey("id", "NUMERIC_TYPE");

// Make an update transaction instance
$upd_PARTICIPANTS = new tNG_multipleUpdate($conn_Wockets);
$tNGs->addTransaction($upd_PARTICIPANTS);
// Register triggers
$upd_PARTICIPANTS->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Update1");
$upd_PARTICIPANTS->registerTrigger("BEFORE", "Trigger_Default_FormValidation", 10, $formValidation);
$upd_PARTICIPANTS->registerTrigger("END", "Trigger_Default_Redirect", 99, "../includes/nxt/back.php");
// Add columns
$upd_PARTICIPANTS->setTable("PARTICIPANTS");
$upd_PARTICIPANTS->addColumn("first_name", "STRING_TYPE", "POST", "first_name");
$upd_PARTICIPANTS->addColumn("last_name", "STRING_TYPE", "POST", "last_name");
$upd_PARTICIPANTS->addColumn("email", "STRING_TYPE", "POST", "email");
$upd_PARTICIPANTS->addColumn("phonenumber", "STRING_TYPE", "POST", "phonenumber");
$upd_PARTICIPANTS->addColumn("birthyear", "NUMERIC_TYPE", "POST", "birthyear");
$upd_PARTICIPANTS->addColumn("gender", "STRING_TYPE", "POST", "gender");
$upd_PARTICIPANTS->addColumn("height", "NUMERIC_TYPE", "POST", "height");
$upd_PARTICIPANTS->addColumn("weight", "NUMERIC_TYPE", "POST", "weight");
$upd_PARTICIPANTS->addColumn("race", "STRING_TYPE", "POST", "race");
$upd_PARTICIPANTS->addColumn("start_date", "DATE_TYPE", "POST", "start_date");
$upd_PARTICIPANTS->addColumn("end_date", "DATE_TYPE", "POST", "end_date");
$upd_PARTICIPANTS->addColumn("notes", "STRING_TYPE", "POST", "notes");
$upd_PARTICIPANTS->setPrimaryKey("id", "NUMERIC_TYPE", "GET", "id");

// Make an instance of the transaction object
$del_PARTICIPANTS = new tNG_multipleDelete($conn_Wockets);
$tNGs->addTransaction($del_PARTICIPANTS);
// Register triggers
$del_PARTICIPANTS->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Delete1");
$del_PARTICIPANTS->registerTrigger("END", "Trigger_Default_Redirect", 99, "../includes/nxt/back.php");
// Add columns
$del_PARTICIPANTS->setTable("PARTICIPANTS");
$del_PARTICIPANTS->setPrimaryKey("id", "NUMERIC_TYPE", "GET", "id");

// Make a logout transaction instance
$logoutTransaction = new tNG_logoutTransaction($conn_Wockets);
$tNGs->addTransaction($logoutTransaction);
// Register triggers
$logoutTransaction->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "GET", "KT_logout_now");
$logoutTransaction->registerTrigger("END", "Trigger_Default_Redirect", 99, "../index.php");
// Add columns
// End of logout transaction instance

// Execute all the registered transactions
$tNGs->executeTransactions();

// Get the transaction recordset
$rsPARTICIPANTS = $tNGs->getRecordset("PARTICIPANTS");
$row_rsPARTICIPANTS = mysql_fetch_assoc($rsPARTICIPANTS);
$totalRows_rsPARTICIPANTS = mysql_num_rows($rsPARTICIPANTS);

// Get the transaction recordset
$rscustom = $tNGs->getRecordset("custom");
$row_rscustom = mysql_fetch_assoc($rscustom);
$totalRows_rscustom = mysql_num_rows($rscustom);
?><!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
<meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1" />
<title>Untitled Document</title>
<script src="../includes/cssmenus2/js/cssmenus.js" type="text/javascript"></script>
<link href="../includes/cssmenus2/skins/interakt_blue/horizontal.css" rel="stylesheet" type="text/css" />
<script src="../includes/common/js/base.js" type="text/javascript"></script>
<script src="../includes/common/js/utility.js" type="text/javascript"></script>

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



<p> </p>
<div id="cssMenu1" class="horizontal" >
  <ul class="interakt_blue">
    <li> <a href="../main.php" title="Logout">Home</a> </li>
    <li> <a href="#" title="Study">Study</a>
        <ul>
          <li> <a href="phones.php" title="Phones">Phones</a> </li>
          <li> <a href="wockets.php" title="Wockets">Wockets</a> </li>
          <li> <a href="participants.php" title="Participants">Participants</a> </li>
      </ul>
    </li>
    <li> <a href="#" title="Export">Actions</a>
        <ul>
          <li> <a href="participant_phone.php" title="Assign phone to participant">Assign Phone</a> </li>
          <li> <a href="participant_wocket.php" title="Assign Wocket">Assign Wocket</a> </li>
          <li> <a href="ExportData.php" title="Export Data">Export Data</a> </li>
      </ul>
    </li>
    <li> <a href="#" title="Advanced">Advanced</a>
        <ul>
          <li> <a href="accounts.php" title="User Accounts">User Accounts</a> </li>
          <li> <a href="Files.php" title="Files">Files</a> </li>
          <li> <a href="phone_stats.php" title="Phone Statistics">Phone Statistics</a> </li>
          <li> <a href="wocket_stats.php" title="Wockets Statistics">Wockets Statistics</a> </li>
      </ul>
    </li>
    <li> <a href="<?php echo $logoutTransaction->getLogoutLink(); ?>" title="">Logout</a> </li>
  </ul>
  <br />
  <script type="text/javascript">
	<!--
    var obj_cssMenu1 = new CSSMenu("cssMenu1");
    obj_cssMenu1.setTimeouts(400, 200, 800);
    obj_cssMenu1.setSubMenuOffset(0, 0, 0, 0);
    obj_cssMenu1.setHighliteCurrent(true);
    obj_cssMenu1.show();
   //-->
  </script>
</div>
<p>&nbsp;</p>


<div class="KT_tng">
  <h1>
    <?php 
// Show IF Conditional region1 
if (@$_GET['id'] == "") {
?>
      <?php echo NXT_getResource("Insert_FH"); ?>
      <?php 
// else Conditional region1
} else { ?>
      <?php echo NXT_getResource("Update_FH"); ?>
      <?php } 
// endif Conditional region1
?>
    PARTICIPANTS </h1>
  <div class="KT_tngform">
    <form method="post" id="form1" action="<?php echo KT_escapeAttribute(KT_getFullUri()); ?>">
      <?php $cnt1 = 0; ?>
      <?php do { ?>
        <?php $cnt1++; ?>
        <?php 
// Show IF Conditional region1 
if (@$totalRows_rsPARTICIPANTS > 1) {
?>
          <h2><?php echo NXT_getResource("Record_FH"); ?> <?php echo $cnt1; ?></h2>
          <?php } 
// endif Conditional region1
?>
        <table cellpadding="2" cellspacing="0" class="KT_tngtable">
          <tr>
            <td class="KT_th"><label for="first_name_<?php echo $cnt1; ?>">First Name:</label></td>
            <td><input type="text" name="first_name_<?php echo $cnt1; ?>" id="first_name_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsPARTICIPANTS['first_name']); ?>" size="32" maxlength="100" />
                <?php echo $tNGs->displayFieldHint("first_name");?> <?php echo $tNGs->displayFieldError("PARTICIPANTS", "first_name", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="last_name_<?php echo $cnt1; ?>">Last Name:</label></td>
            <td><input type="text" name="last_name_<?php echo $cnt1; ?>" id="last_name_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsPARTICIPANTS['last_name']); ?>" size="32" maxlength="100" />
                <?php echo $tNGs->displayFieldHint("last_name");?> <?php echo $tNGs->displayFieldError("PARTICIPANTS", "last_name", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="email_<?php echo $cnt1; ?>">Email:</label></td>
            <td><input type="text" name="email_<?php echo $cnt1; ?>" id="email_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsPARTICIPANTS['email']); ?>" size="32" maxlength="100" />
                <?php echo $tNGs->displayFieldHint("email");?> <?php echo $tNGs->displayFieldError("PARTICIPANTS", "email", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="phonenumber_<?php echo $cnt1; ?>">Phone Number:</label></td>
            <td><input type="text" name="phonenumber_<?php echo $cnt1; ?>" id="phonenumber_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsPARTICIPANTS['phonenumber']); ?>" size="32" maxlength="100" />
                <?php echo $tNGs->displayFieldHint("phonenumber");?> <?php echo $tNGs->displayFieldError("PARTICIPANTS", "phonenumber", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="birthyear_<?php echo $cnt1; ?>">Birthyear:</label></td>
            <td><input type="text" name="birthyear_<?php echo $cnt1; ?>" id="birthyear_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsPARTICIPANTS['birthyear']); ?>" size="7" />
                <?php echo $tNGs->displayFieldHint("birthyear");?> <?php echo $tNGs->displayFieldError("PARTICIPANTS", "birthyear", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="gender_<?php echo $cnt1; ?>">Gender:</label></td>
            <td><select name="gender_<?php echo $cnt1; ?>" id="gender_<?php echo $cnt1; ?>">
              <option value="male" <?php if (!(strcmp("male", KT_escapeAttribute($row_rsPARTICIPANTS['gender'])))) {echo "SELECTED";} ?>>male</option>
              <option value="female" <?php if (!(strcmp("female", KT_escapeAttribute($row_rsPARTICIPANTS['gender'])))) {echo "SELECTED";} ?>>female</option>
            </select>
                <?php echo $tNGs->displayFieldError("PARTICIPANTS", "gender", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="height_<?php echo $cnt1; ?>">Height:</label></td>
            <td><input type="text" name="height_<?php echo $cnt1; ?>" id="height_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsPARTICIPANTS['height']); ?>" size="7" />
                <?php echo $tNGs->displayFieldHint("height");?> <?php echo $tNGs->displayFieldError("PARTICIPANTS", "height", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="weight_<?php echo $cnt1; ?>">Weight:</label></td>
            <td><input type="text" name="weight_<?php echo $cnt1; ?>" id="weight_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsPARTICIPANTS['weight']); ?>" size="7" />
                <?php echo $tNGs->displayFieldHint("weight");?> <?php echo $tNGs->displayFieldError("PARTICIPANTS", "weight", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="race_<?php echo $cnt1; ?>">Race:</label></td>
            <td><select name="race_<?php echo $cnt1; ?>" id="race_<?php echo $cnt1; ?>">
              <option value="white" <?php if (!(strcmp("white", KT_escapeAttribute($row_rsPARTICIPANTS['race'])))) {echo "SELECTED";} ?>>White</option>
              <option value="africanamerican" <?php if (!(strcmp("africanamerican", KT_escapeAttribute($row_rsPARTICIPANTS['race'])))) {echo "SELECTED";} ?>>African American</option>
              <option value="asian" <?php if (!(strcmp("asian", KT_escapeAttribute($row_rsPARTICIPANTS['race'])))) {echo "SELECTED";} ?>>Asian</option>
              <option value="hispanic" <?php if (!(strcmp("hispanic", KT_escapeAttribute($row_rsPARTICIPANTS['race'])))) {echo "SELECTED";} ?>>Hispanic</option>
              <option value="americanindian" <?php if (!(strcmp("americanindian", KT_escapeAttribute($row_rsPARTICIPANTS['race'])))) {echo "SELECTED";} ?>>American Indian</option>
              <option value="alaskanative" <?php if (!(strcmp("alaskanative", KT_escapeAttribute($row_rsPARTICIPANTS['race'])))) {echo "SELECTED";} ?>>Alaska Native</option>
              <option value="nativehawaiian" <?php if (!(strcmp("nativehawaiian", KT_escapeAttribute($row_rsPARTICIPANTS['race'])))) {echo "SELECTED";} ?>>Native Hawaiian</option>
              <option value="other" <?php if (!(strcmp("other", KT_escapeAttribute($row_rsPARTICIPANTS['race'])))) {echo "SELECTED";} ?>>Other</option>
            </select>
                <?php echo $tNGs->displayFieldError("PARTICIPANTS", "race", $cnt1); ?> </td>
          </tr>
<tr>
            <td class="KT_th"><label for="start_date_<?php echo $cnt1; ?>">Start_date:</label></td>
            <td><input type="text" name="start_date_<?php echo $cnt1; ?>" id="start_date_<?php echo $cnt1; ?>" value="<?php echo KT_formatDate($row_rsPARTICIPANTS['start_date']); ?>" size="10" maxlength="22" />
                <?php echo $tNGs->displayFieldHint("start_date");?> <?php echo $tNGs->displayFieldError("PARTICIPANTS", "start_date", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="end_date_<?php echo $cnt1; ?>">End_date:</label></td>
            <td><input type="text" name="end_date_<?php echo $cnt1; ?>" id="end_date_<?php echo $cnt1; ?>" value="<?php echo KT_formatDate($row_rsPARTICIPANTS['end_date']); ?>" size="10" maxlength="22" />
                <?php echo $tNGs->displayFieldHint("end_date");?> <?php echo $tNGs->displayFieldError("PARTICIPANTS", "end_date", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="notes_<?php echo $cnt1; ?>">Notes:</label></td>
            <td><textarea name="notes_<?php echo $cnt1; ?>" id="notes_<?php echo $cnt1; ?>" cols="50" rows="5"><?php echo KT_escapeAttribute($row_rsPARTICIPANTS['notes']); ?></textarea>
                <?php echo $tNGs->displayFieldHint("notes");?> <?php echo $tNGs->displayFieldError("PARTICIPANTS", "notes", $cnt1); ?> </td>
          </tr>
        </table>
        <input type="hidden" name="kt_pk_PARTICIPANTS_<?php echo $cnt1; ?>" class="id_field" value="<?php echo KT_escapeAttribute($row_rsPARTICIPANTS['kt_pk_PARTICIPANTS']); ?>" />
        <?php } while ($row_rsPARTICIPANTS = mysql_fetch_assoc($rsPARTICIPANTS)); ?>
      <div class="KT_bottombuttons">
        <div>
          <?php 
      // Show IF Conditional region1
      if (@$_GET['id'] == "") {
      ?>
            <input type="submit" name="KT_Insert1" id="KT_Insert1" value="<?php echo NXT_getResource("Insert_FB"); ?>" />
            <?php 
      // else Conditional region1
      } else { ?>
            <div class="KT_operations">
              <input type="submit" name="KT_Insert1" value="<?php echo NXT_getResource("Insert as new_FB"); ?>" onclick="nxt_form_insertasnew(this, 'id')" />
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
