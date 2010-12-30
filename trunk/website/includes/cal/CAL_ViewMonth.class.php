<?php
class CAL_ViewMonth extends CAL_ViewBase {

	function _setInterval() {
		$selectedDate = CAL_addDate($this->selectedDate, 0, 'd');
		$this->startDate = CAL_extract('Y-m-01',$this->selectedDate) . ' 00:00:00';
		$this->endDate = CAL_addDate($this->startDate, 1, 'm');
		$tmp_day = CAL_getWeekDay($this->startDate, $this->calendar->getMondayFirst());
		$this->startDate = CAL_addDate($this->startDate,-$tmp_day, 'd');
		$tmp_day = CAL_getWeekDay(CAL_addDate($this->endDate, -1, 'd'), $this->calendar->getMondayFirst());
		$this->endDate = CAL_addDate($this->endDate,(6-$tmp_day), 'd',true);
	}

	function _prepareNav() {
		$selectedDate = CAL_addDate($this->selectedDate, 0, 'd');

		$tmp_date = CAL_addDate($selectedDate, -1, 'm');
		while (CAL_extract('m', $selectedDate) == CAL_extract('m', $tmp_date)) {
			$tmp_date = CAL_addDate($tmp_date, -1, 'd');
		}
		$tmp_date = KT_convertDate($tmp_date, 'yyyy-mm-dd HH:ii:ss', $GLOBALS['KT_db_date_format']);
		$tmp_url = KT_addReplaceParam(KT_getFullUri(), $this->calendar->getDateParam(), $tmp_date);
		$this->data['nav']['prev_link'] = $tmp_url;
		
		$tmp_date = CAL_addDate($selectedDate, 1, 'm');
		while (CAL_extract('m', $selectedDate)+2 == CAL_extract('m', $tmp_date)) {
			$tmp_date = CAL_addDate($tmp_date, -1, 'd');
		}
		$tmp_date = KT_convertDate($tmp_date, 'yyyy-mm-dd HH:ii:ss', $GLOBALS['KT_db_date_format']);
		$tmp_url = KT_addReplaceParam(KT_getFullUri(), $this->calendar->getDateParam(), $tmp_date);
		$this->data['nav']['next_link'] = $tmp_url;
		
		$this->data['nav']['title']['year'] = CAL_extract('Y', $selectedDate);
		$this->data['nav']['title']['month'] = CAL_extract('F', $selectedDate);
		
		$this->data['nav']['title']['weekday'] = array('Monday','Tuesday','Wednesday','Thursday','Friday','Saturday');
		if ($this->calendar->getMondayFirst()) {
			$this->data['nav']['title']['weekday'][] = 'Sunday';
		} else {
			array_unshift($this->data['nav']['title']['weekday'], 'Sunday');
		}
	}

	function _renderData() {
		$view = 'month';
?>
<table class="main_cal detail_cal month_cal kt_add_tooltips" cellpadding="0" cellspacing="0" border="0">
	<tr class="nav_cal">
		<th class="np_cal">
			<a href="<?php echo CAL_XHTML_Url($this->data['nav']['prev_link']);?>" title="<?php echo CAL_getResource('PREV_CALENDAR_TITLE');?>"><?php echo CAL_getResource('PREV_CALENDAR');?></a>
		</th>
		<th colspan="5">
		<?php echo CAL_getResource($this->data['nav']['title']['month']);?> <?php echo $this->data['nav']['title']['year'];?>
		</th>
		<th class="np_cal">
			<a href="<?php echo CAL_XHTML_Url($this->data['nav']['next_link']);?>" title="<?php echo CAL_getResource('NEXT_CALENDAR_TITLE');?>"><?php echo CAL_getResource('NEXT_CALENDAR');?></a>
		</th>
	</tr>
	<tr class="days_cal">
	<?php
		foreach ($this->data['nav']['title']['weekday'] as $key => $monthName) {
	?>
	<th><?php echo CAL_getResource($monthName);?></th>
	<?php
	}
	?>
	</tr>
	
	<tr class="weeks_cal">
	<?php
	$j=0;
	$time_format = str_replace(':ss', '',$GLOBALS['KT_screen_time_format_internal']);
	$data_body_count = count($this->data['body']);
	foreach($this->data['body'] as $cDate => $data) {
		$j++;
		
		require(dirname(realpath(__FILE__)). '/CAL_mwCell.inc.php');
		

		if ($j % 7 == 0) {
			if ($data_body_count > $j){
				echo '</tr><tr class="weeks_cal">';
			}
		}
	}
	?>
	</tr>
</table>
<?php
	}
}
?>