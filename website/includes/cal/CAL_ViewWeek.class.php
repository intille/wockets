<?php
class CAL_ViewWeek extends CAL_ViewBase
{

	function _setInterval() {
		$selectedDate = CAL_addDate($this->selectedDate, 0, 'd');
		$this->startDate = CAL_getWeekDay($selectedDate, $this->calendar->getMondayFirst());
		$this->startDate = CAL_addDate($selectedDate, -$this->startDate, 'd');
		$this->endDate = CAL_addDate($this->startDate, 7, 'd');
	}

	function _prepareNav() {
		$selectedDate = CAL_addDate($this->selectedDate, 0, 'd');
		
		$tmp_date = CAL_addDate($selectedDate, -7, 'd');
		$tmp_date = KT_convertDate($tmp_date, 'yyyy-mm-dd HH:ii:ss', $GLOBALS['KT_db_date_format']);
		$tmp_url = KT_addReplaceParam(KT_getFullUri(), $this->calendar->getDateParam(), $tmp_date);
		$this->data['nav']['prev_link'] = $tmp_url;
		
		$tmp_date = CAL_addDate($selectedDate, 7, 'd');
		$tmp_date = KT_convertDate($tmp_date, 'yyyy-mm-dd HH:ii:ss', $GLOBALS['KT_db_date_format']);
		$tmp_url = KT_addReplaceParam(KT_getFullUri(), $this->calendar->getDateParam(), $tmp_date);
		$this->data['nav']['next_link'] = $tmp_url;
		
		$tmp_date = $this->startDate;
		$this->data['nav']['title']['start']['weekday'] = CAL_extract('l',$tmp_date);
		$this->data['nav']['title']['start']['year'] = CAL_extract('Y',$tmp_date);
		$this->data['nav']['title']['start']['month'] = CAL_extract('F',$tmp_date);
		$this->data['nav']['title']['start']['day'] = CAL_extract('d',$tmp_date);
		
		$tmp_days = 3;
		if ($this->calendar->getMondayFirst() == false) {
			$tmp_days = 4;
		}
		$tmp_date = CAL_addDate($this->startDate,$tmp_days,'d');
		
		$this->data['nav']['title']['week'] = CAL_extract('W', $tmp_date);
		
		$tmp_date = CAL_addDate($this->endDate, -1, 'd');
		$this->data['nav']['title']['end']['weekday'] = CAL_extract('l',$tmp_date);
		$this->data['nav']['title']['end']['year'] = CAL_extract('Y',$tmp_date);
		$this->data['nav']['title']['end']['month'] = CAL_extract('F',$tmp_date);
		$this->data['nav']['title']['end']['day'] = CAL_extract('d',$tmp_date);
	}

	function _renderData() {
		$view = 'week';
?>
<table class="main_cal detail_cal week_cal kt_add_tooltips" border="0" cellspacing="0" cellpadding="0">
	<tr class="nav_cal">
		<th class="np_cal">
			<a href="<?php echo CAL_XHTML_Url($this->data['nav']['prev_link']);?>" title="<?php echo CAL_getResource('PREV_CALENDAR_TITLE');?>"><?php echo CAL_getResource('PREV_CALENDAR');?></a>
		</th>
		<th>
			<div>
				<?php echo CAL_getResource($this->data['nav']['title']['start']['month']);?> <?php echo $this->data['nav']['title']['start']['day'];?>
				-
				<?php echo CAL_getResource($this->data['nav']['title']['end']['month']);?> <?php echo $this->data['nav']['title']['end']['day'];?>
			</div>
			<div>
				<?php echo CAL_getResource('WEEK');?> <?php echo $this->data['nav']['title']['week'];?>
			</div>
		</th>
		<th class="np_cal">
			<a href="<?php echo CAL_XHTML_Url($this->data['nav']['next_link']);?>" title="<?php echo CAL_getResource('NEXT_CALENDAR_TITLE');?>"><?php echo CAL_getResource('NEXT_CALENDAR');?></a>
		</th>
	</tr>
	<tr class="weeks_cal">
	<?php
	$j=0;
	$time_format = str_replace(':ss', '',$GLOBALS['KT_screen_time_format_internal']);
	$lastMonth = '';
	foreach($this->data['body'] as $cDate => $data) {
		$j++;
		
		require(dirname(realpath(__FILE__)). '/CAL_mwCell.inc.php');
		
		if ($j % 3 == 0) {
			echo '</tr><tr class="weeks_cal">';
		}
	}
	?>
	<td colspan="2">&nbsp;</td>
	</tr>
</table>
<?php
	}
}
?>