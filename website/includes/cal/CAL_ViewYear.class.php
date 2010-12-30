<?php
class CAL_ViewYear extends CAL_ViewBase
{
	var $month;
	var $day;
	var $year;
	var $dateParameter;
	
	function _setInterval() {
		$year = CAL_extract('Y', $this->selectedDate);
		$this->startDate = $year.'-01-01 00:00:00';
		$this->endDate = ((int)($year+1)).'-01-01 00:00:00';
	}
	
	function _prepareNav() {
		$selectedDate = CAL_addDate($this->selectedDate, 0, 'd');

		$tmp_date = CAL_addDate($selectedDate, -1, 'Y');
		if (CAL_extract('m', $selectedDate) != CAL_extract('m', $tmp_date)) {
			$tmp_date = CAL_addDate($tmp_date, -1, 'd');
		}
		$tmp_date = KT_convertDate($tmp_date, 'yyyy-mm-dd HH:ii:ss', $GLOBALS['KT_db_date_format']);
		$tmp_url = KT_addReplaceParam(KT_getFullUri(), $this->calendar->getDateParam(), $tmp_date);
		$this->data['nav']['prev_link'] = $tmp_url;
		
		$tmp_date = CAL_addDate($selectedDate, 1, 'Y');
		if (CAL_extract('m', $selectedDate) != CAL_extract('m', $tmp_date)) {
			$tmp_date = CAL_addDate($tmp_date, -1, 'd');
		}
		$tmp_date = KT_convertDate($tmp_date, 'yyyy-mm-dd HH:ii:ss', $GLOBALS['KT_db_date_format']);
		$tmp_url = KT_addReplaceParam(KT_getFullUri(), $this->calendar->getDateParam(), $tmp_date);
		$this->data['nav']['next_link'] = $tmp_url;
		
		$this->data['nav']['title']['year'] = CAL_extract('Y', $selectedDate);
	}
	
	function _computeEvents() {
	}
	
	function _transformEvents() {
		//print_r($this->data);
	}
	
	function _renderData() {
?>
<table class="year_cal kt_add_tooltips" cellpadding="0" cellspacing="0" border="0">
	<tr class="nav_cal">
		<th class="np_cal"><a href="<?php echo CAL_XHTML_Url($this->data['nav']['prev_link']);?>" title="<?php echo CAL_getResource('PREV_CALENDAR_TITLE');?>"><?php echo CAL_getResource('PREV_CALENDAR');?></a></th>
		<th><?php echo $this->data['nav']['title']['year'];?></th>
		<th class="np_cal"><a href="<?php echo CAL_XHTML_Url($this->data['nav']['next_link']);?>" title="<?php echo CAL_getResource('NEXT_CALENDAR_TITLE');?>"><?php echo CAL_getResource('NEXT_CALENDAR');?></a></th>
			</tr><!-- here -->
<?php
		$calMonth = new CAL_CalendarNugget($this->calendar->getRelPath());
		
		$calMonth->setFromYearView(true); 
		
		$calMonth->setDateParam($this->calendar->getDateParam());
		$calMonth->setViewModParam($this->calendar->getViewModParam());
					
		$calMonth->setRecordset($this->calendar->getRecordsetName());
		$calMonth->setField("ID", $this->calendar->getFieldName('ID'));
		$calMonth->setField("TITLE", $this->calendar->getFieldName('TITLE'));
		$calMonth->setField("START_DATE", $this->calendar->getFieldName('START_DATE'));
		$calMonth->setField("END_DATE", $this->calendar->getFieldName('END_DATE')); 
		$calMonth->setField("RECURRING", $this->calendar->getFieldName('RECURRING')); 
						
		$calMonth->setNewEventEnabled($this->calendar->getNewEventEnabledExp());  
		$calMonth->setNewEventLink($this->calendar->getNewEventLink());
		$calMonth->setMondayFirst($this->calendar->getMondayFirst());
		$calMonth->setViewWeekNo($this->calendar->getViewWeekNo());
		$cDate = $this->startDate;
		for ($i=0; $i<12; $i++) {
			if ($i%3==0 && $i>0) {
				echo '</tr><tr class="i'.$i.'">'."\n";
			} else if ($i==0) {
				echo '<tr class="i'.$i.'">'."\n";
			}
		?>
		<td valign="top">
		<?php
			$calMonth->forceDateParam($cDate); 
			$calMonth->render();
			$cDate = CAL_addDate($cDate, 1, 'm');
		?>
		</td>
		<?php
		}
		?>
		</tr>
		</table>
<?php
	}

}
?>