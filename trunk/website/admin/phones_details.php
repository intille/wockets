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
$formValidation->addField("imei", true, "text", "", "", "", "");
$formValidation->addField("model", true, "text", "", "", "", "");
$tNGs->prepareValidation($formValidation);
// End trigger

// Make an insert transaction instance
$ins_PHONES = new tNG_multipleInsert($conn_Wockets);
$tNGs->addTransaction($ins_PHONES);
// Register triggers
$ins_PHONES->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Insert1");
$ins_PHONES->registerTrigger("BEFORE", "Trigger_Default_FormValidation", 10, $formValidation);
$ins_PHONES->registerTrigger("END", "Trigger_Default_Redirect", 99, "../includes/nxt/back.php");
// Add columns
$ins_PHONES->setTable("PHONES");
$ins_PHONES->addColumn("imei", "STRING_TYPE", "POST", "imei");
$ins_PHONES->addColumn("model", "STRING_TYPE", "POST", "model");
$ins_PHONES->addColumn("notes", "STRING_TYPE", "POST", "notes");
$ins_PHONES->setPrimaryKey("id", "NUMERIC_TYPE");

// Make an update transaction instance
$upd_PHONES = new tNG_multipleUpdate($conn_Wockets);
$tNGs->addTransaction($upd_PHONES);
// Register triggers
$upd_PHONES->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Update1");
$upd_PHONES->registerTrigger("BEFORE", "Trigger_Default_FormValidation", 10, $formValidation);
$upd_PHONES->registerTrigger("END", "Trigger_Default_Redirect", 99, "../includes/nxt/back.php");
// Add columns
$upd_PHONES->setTable("PHONES");
$upd_PHONES->addColumn("imei", "STRING_TYPE", "POST", "imei");
$upd_PHONES->addColumn("model", "STRING_TYPE", "POST", "model");
$upd_PHONES->addColumn("notes", "STRING_TYPE", "POST", "notes");
$upd_PHONES->setPrimaryKey("id", "NUMERIC_TYPE", "GET", "id");

// Make an instance of the transaction object
$del_PHONES = new tNG_multipleDelete($conn_Wockets);
$tNGs->addTransaction($del_PHONES);
// Register triggers
$del_PHONES->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Delete1");
$del_PHONES->registerTrigger("END", "Trigger_Default_Redirect", 99, "../includes/nxt/back.php");
// Add columns
$del_PHONES->setTable("PHONES");
$del_PHONES->setPrimaryKey("id", "NUMERIC_TYPE", "GET", "id");

// Execute all the registered transactions
$tNGs->executeTransactions();

// Get the transaction recordset
$rsPHONES = $tNGs->getRecordset("PHONES");
$row_rsPHONES = mysql_fetch_assoc($rsPHONES);
$totalRows_rsPHONES = mysql_num_rows($rsPHONES);
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
    PHONES </h1>
  <div class="KT_tngform">
    <form method="post" id="form1" action="<?php echo KT_escapeAttribute(KT_getFullUri()); ?>">
      <?php $cnt1 = 0; ?>
      <?php do { ?>
        <?php $cnt1++; ?>
        <?php 
// Show IF Conditional region1 
if (@$totalRows_rsPHONES > 1) {
?>
          <h2><?php echo NXT_getResource("Record_FH"); ?> <?php echo $cnt1; ?></h2>
          <?php } 
// endif Conditional region1
?>
        <table cellpadding="2" cellspacing="0" class="KT_tngtable">
          <tr>
            <td class="KT_th"><label for="imei_<?php echo $cnt1; ?>">IMEI:</label></td>
            <td><input type="text" name="imei_<?php echo $cnt1; ?>" id="imei_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsPHONES['imei']); ?>" size="32" maxlength="100" />
                <?php echo $tNGs->displayFieldHint("imei");?> <?php echo $tNGs->displayFieldError("PHONES", "imei", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="model_<?php echo $cnt1; ?>">Model:</label></td>
            <td><select name="model_<?php echo $cnt1; ?>" id="model_<?php echo $cnt1; ?>">
              <option value="HTC Diamond Touch" <?php if (!(strcmp("HTC Diamond Touch", KT_escapeAttribute($row_rsPHONES['model'])))) {echo "SELECTED";} ?>>HTC Diamond Touch</option>
              <option value="HTC Diamond Touch2" <?php if (!(strcmp("HTC Diamond Touch2", KT_escapeAttribute($row_rsPHONES['model'])))) {echo "SELECTED";} ?>>HTC Diamond Touch2</option>
            </select>
                <?php echo $tNGs->displayFieldError("PHONES", "model", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="notes_<?php echo $cnt1; ?>">Notes:</label></td>
            <td><textarea name="notes_<?php echo $cnt1; ?>" id="notes_<?php echo $cnt1; ?>" cols="50" rows="5"><?php echo KT_escapeAttribute($row_rsPHONES['notes']); ?></textarea>
                <?php echo $tNGs->displayFieldHint("notes");?> <?php echo $tNGs->displayFieldError("PHONES", "notes", $cnt1); ?> </td>
          </tr>
        </table>
        <input type="hidden" name="kt_pk_PHONES_<?php echo $cnt1; ?>" class="id_field" value="<?php echo KT_escapeAttribute($row_rsPHONES['kt_pk_PHONES']); ?>" />
        <?php } while ($row_rsPHONES = mysql_fetch_assoc($rsPHONES)); ?>
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
