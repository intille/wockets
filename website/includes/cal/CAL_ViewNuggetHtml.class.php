<?php
class CAL_ViewNuggetHtml extends CAL_ViewBase
{

	function _setInterval() {
		$selectedDate = CAL_addDate($this->selectedDate, 0, 'd');
		if ($this->calendar->forcedDate != '') {
			$selectedDate = CAL_addDate($this->calendar->forcedDate, 0, 'd');
		}
		// Set StartDate and EndDate
		$this->startDate = CAL_extract('Y-m-01',$selectedDate) . ' 00:00:00';
		$this->endDate = CAL_addDate($this->startDate, 1, 'm');
		$tmp_day = CAL_getWeekDay($this->startDate, $this->calendar->getMondayFirst());
		$this->startDate = CAL_addDate($this->startDate, -$tmp_day, 'd');
		$lastDayOfCurrMonth = CAL_addDate($this->endDate, -1, 'd');
		$tmp_day = CAL_getWeekDay($lastDayOfCurrMonth, $this->calendar->getMondayFirst());
		$this->endDate = CAL_addDate($this->endDate, (6-$tmp_day), 'd');
	}
	
	function _prepareNav() {
		$selectedDate = CAL_addDate($this->selectedDate, 0, 'd');
		if ($this->calendar->forcedDate != '') {
			$selectedDate = CAL_addDate($this->calendar->forcedDate, 0, 'd');
		}
		
		$this->data = array();
		$this->data['nav'] = array();
		$this->data['body'] = array();

		$tmp_date = $selectedDate;
		$tmp_date = KT_convertDate($tmp_date, 'yyyy-mm-dd HH:ii:ss', $GLOBALS['KT_db_date_format']);
		$tmp_url = KT_addReplaceParam(KT_getFullUri(), $this->calendar->getDateParam(), $tmp_date);
		$this->data['nav']['curr_link'] = $tmp_url;

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
		
		$this->data['nav']['title']['week'] = array('Mon','Tue','Wed','Thu','Fri','Sat');
		if ($this->calendar->getMondayFirst()) {
			$this->data['nav']['title']['week'][] = 'Sun';
		} else {
			array_unshift($this->data['nav']['title']['week'], 'Sun');
		}
	}
	
	function _renderData() {

?>
<table class="main_cal nugget_cal kt_add_tooltips" cellpadding="0" cellspacing="0" border="0">
	<tr class="nav_cal">
		<th class="np_cal">
		<?php
			if ($this->calendar->getFromYearView() == false) {
		?>
			<a href="<?php echo CAL_XHTML_Url($this->data['nav']['prev_link']);?>" title="<?php echo CAL_getResource('PREV_CALENDAR_TITLE');?>"><?php echo CAL_getResource('PREV_CALENDAR');?></a>
		<?php
			}
		?>
		</th>
		<th colspan="<?php if ($this->calendar->getViewWeekNo()) { echo "6"; } else { echo"5"; } ?>">
		<?php
			if ($this->calendar->getFromYearView() == false) {
		?>
			<?php echo CAL_getResource($this->data['nav']['title']['month']);?> <?php echo $this->data['nav']['title']['year'];?>
		<?php
			} else {
				$mLink = $this->data['nav']['curr_link'];
				$mLink = KT_addReplaceParam($mLink, $this->calendar->getViewModParam(), 'month');
			?>
			<a href="<?php echo CAL_XHTML_Url($mLink);?>" title="<?php echo CAL_getResource('MONTH_WEEK');?>"><?php echo CAL_getResource($this->data['nav']['title']['month']);?> <?php echo $this->data['nav']['title']['year'];?></a>
		<?php
			}
		?>
		</th>
		<th class="np_cal">
		<?php
			if ($this->calendar->getFromYearView() == false) {
		?>
			<a href="<?php echo CAL_XHTML_Url($this->data['nav']['next_link']);?>" title="<?php echo CAL_getResource('NEXT_CALENDAR_TITLE');?>"><?php echo CAL_getResource('NEXT_CALENDAR');?></a>
		<?php
			}
		?>
		</th>
	</tr>
	<tr class="days_cal">
		<?php if ($this->calendar->getViewWeekNo()) { ?>
		<th class="wkno_cal">
			<?php echo CAL_getResource('wk');?>
		</th>
		<?php } ?>
		<?php
			foreach ($this->data['nav']['title']['week'] as $key => $monthName) {
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
		if ($j % 7 == 0 && $this->calendar->getViewWeekNo()) {
	?>
		<td class="wkno_cal">
			<?php
			if ($this->calendar->getMondayFirst()){
				$tmp_link = KT_addReplaceParam($data['link'], $this->calendar->getViewModParam(), 'week');
				$tmp_date = CAL_addDate($cDate,5,'d');
			} else {
				$tmp_date = CAL_addDate($cDate, 1, 'd');
				$tmp_link = KT_addReplaceParam($this->data['body'][$tmp_date]['link'], $this->calendar->getViewModParam(), 'week');
				$tmp_date = CAL_addDate($cDate,6,'d');
			}
			if ($this->calendar->detailPage != '') {
				$tmp_link = CAL_glueQueryStrings($this->calendar->detailPage, $tmp_link);
			}
			$tmp_link = str_replace("&", "&amp;", $tmp_link);
			?>
			<a href="<?php echo CAL_XHTML_Url($tmp_link);?>" title="<?php echo CAL_getResource('VIEW_WEEK');?>" <?php if ($this->calendar->detailTarget != '') { ?>target="<?php echo $this->calendar->detailTarget; ?>" <?php } ?>><?php echo CAL_extract('W',$tmp_date);?></a>
		</td>
	<?php
		}
	?>
	<?php
		if ($this->calendar->getFromYearView() == false || !$data['othermonth']) {
	?>
	<td class="none_cal<?php if (count($data['event']) > 0) echo " hasevent_cal";?><?php if ($data['othermonth']) echo " othermonth_cal";?><?php if ($data['weekend'] && $data['othermonth'] == false) echo " weekend_cal";?><?php if (isset($data['selected'])) echo " selected_cal";?><?php if (isset($data['today'])) echo " today_cal";?>">
		<div>
			<?php 
				if (count($data['event']) > 0 || $this->calendar->getNewEventEnabled()) { 
					$tmp_link = $data['link'];
					if ($this->calendar->detailPage != '') {
						$detailPage = KT_DynamicData($this->calendar->detailPage, '', '', false, array(), false);
						$tmp_link = CAL_glueQueryStrings($detailPage, $tmp_link);
					}
					$tmp_link = str_replace("&", "&amp;", $tmp_link);
			?>
		<a href="<?php echo CAL_XHTML_Url($tmp_link);?>" title="<?php echo $data['title'];?>" <?php if ($this->calendar->detailTarget != '') { ?>target="<?php echo $this->calendar->detailTarget; ?>" <?php } ?>><?php echo CAL_getResource($data['day']);?></a>
			<?php
			} else {
			?>
				<?php echo CAL_getResource($data['day']);?>
			<?php
			}
			?>
		</div>
	</td>
	<?php
		} else {
	?>
		<td>&nbsp;</td>
	<?php
		}
	?>
	<?php
		$j++;
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