<?php
class CAL_ViewDay extends CAL_ViewBase
{

	function _setInterval() {
		$this->startDate = CAL_addDate($this->selectedDate, 0, 'd');
		$this->endDate = CAL_addDate($this->startDate, 1, 'd');
	}

	function _prepareNav() {
		$selectedDate = CAL_addDate($this->selectedDate, 0, 'd');

		$tmp_date = CAL_addDate($this->startDate, -1, 'd');
		$tmp_date = KT_convertDate($tmp_date, 'yyyy-mm-dd HH:ii:ss', $GLOBALS['KT_db_date_format']);
		$tmp_url = KT_addReplaceParam(KT_getFullUri(), $this->calendar->getDateParam(), $tmp_date);
		$this->data['nav']['prev_link'] = $tmp_url;
		
		$tmp_date = $this->endDate;
		$tmp_date = KT_convertDate($tmp_date, 'yyyy-mm-dd HH:ii:ss', $GLOBALS['KT_db_date_format']);
		$tmp_url = KT_addReplaceParam(KT_getFullUri(), $this->calendar->getDateParam(), $tmp_date);
		$this->data['nav']['next_link'] = $tmp_url;
		
		$this->data['nav']['title']['day'] = CAL_extract('d', $selectedDate);
		$this->data['nav']['title']['month'] = CAL_extract('F', $selectedDate);
		$this->data['nav']['title']['year'] = CAL_extract('Y', $selectedDate);
		$this->data['nav']['title']['weekday'] = CAL_extract('l', $selectedDate);
	}
	
	function _transformEvents() {
		$selectedDate = CAL_addDate($this->selectedDate, 0, 'd');
		
		$tmpBody = $this->data['body'];
		$this->data['body'] = array();
		$tmpBody = array_pop($tmpBody);
		if (is_array($tmpBody)) {
			$tmpBody = array_pop($tmpBody);
		} else {
			$tmpBody = array();
		}
		usort($tmpBody, "CAL_compareEvents");
		$tmp_date = $this->startDate;
		$min_hour = CAL_addDate($this->startDate, $this->calendar->getStartHour(), 'H');
		$max_hour = CAL_addDate($this->startDate, $this->calendar->getEndHour(), 'H');
		$col_pos_arr = array();
		for($evIdx=0;$evIdx<count($tmpBody);$evIdx++) {
			$tmp_hour = CAL_roundHour($tmpBody[$evIdx]['end'], 'up');
			if ($tmp_hour > $max_hour) {
				$max_hour = $tmp_hour;
			}
			$tmp_hour = CAL_roundHour($tmpBody[$evIdx]['start'], 'down');
			if ($tmp_hour < $min_hour) {
				$min_hour = $tmp_hour;
			}
			$pos = 0;
			$tmp_startDate = CAL_roundHour($tmpBody[$evIdx]['start'],'down');
			$tmp_endDate = CAL_roundHour($tmpBody[$evIdx]['end'],'up');
			for ($i=0;$i<count($col_pos_arr);$i++) {
				$found_pos = true;
				for($j=0;$j<count($col_pos_arr[$i]);$j++) {
					$startDate1= CAL_roundHour($tmpBody[$col_pos_arr[$i][$j]]['start'],'down');
					$endDate1= CAL_roundHour($tmpBody[$col_pos_arr[$i][$j]]['end'],'up');
					if (CAL_DateIntersect($startDate1, $endDate1, $tmp_startDate, $tmp_endDate)) {
						$pos++;
						$found_pos = false;
						break;
					}
				}
				if ($found_pos) {
					break;
				}
			}
			$col_pos_arr[$pos][] = $evIdx;
			$tmpBody[$evIdx]['position'] = $pos;
			
			$tmp_hour1 = CAL_roundHour($tmpBody[$evIdx]['start'], 'down');
			$tmp_hour2 = CAL_roundHour($tmpBody[$evIdx]['end'], 'up');
			$tmpBody[$evIdx]['length'] = (int)(2*CAL_hourDiff($tmp_hour1, $tmp_hour2));
			$this->data['body'][$tmp_hour]['event'][] = $tmpBody[$evIdx];
		}
		$this->data['width'] = count($col_pos_arr);
		$this->data['height'] = (int)(2*CAL_hourDiff($min_hour, $max_hour));

		$c_hour=$min_hour;
		while($c_hour<$max_hour) {

			if ($this->calendar->getNewEventEnabled()) {
				$page = $this->calendar->getNewEventLink();
				if ($this->calendar->type == 'view') {
					if ($this->calendar->getSendKTBack() == true) {
						$page = KT_addReplaceParam($page, 'KT_back', 1);
					} else {
						foreach ($_GET as $key => $value) {
							$page = CAL_glueQueryStrings($page, $key . '=' . $value);
							//$page = KT_addReplaceParam($page, $key, $value);
						}
					}
				}
				$page = KT_addReplaceParam($page, $this->calendar->getDateParam(), KT_convertDate($c_hour, 'yyyy-mm-dd HH:ii:ss', $GLOBALS['KT_db_date_format']));
				$page = KT_addReplaceParam($page, $this->calendar->getDateParam().'_sf', KT_convertDate($c_hour, 'yyyy-mm-dd HH:ii:ss', $GLOBALS['KT_screen_date_format'].' '.$GLOBALS['KT_screen_time_format_internal']));
				$this->data['body'][$c_hour]['add'] = $page;
			}
			
			if (!isset($this->data['body'][$c_hour]['event'])) {
				$this->data['body'][$c_hour]['event'] = array();
			} else {
				usort($this->data['body'][$c_hour]['event'], "CAL_compareEvents");
			}

			$c_hour = CAL_addDate($c_hour, 30, 'i');
		}
        
		ksort($this->data['body']);
		//print_r($this->data['body']); print_r($min_hour.'->'.$max_hour); exit;
	}

	function _renderData() {
		$time_format = str_replace(':ss', '',$GLOBALS['KT_screen_time_format_internal']);
?>
<table class="main_cal detail_cal day_cal kt_add_tooltips" border="0" cellspacing="0" cellpadding="0">
	<tr class="nav_cal">
		<th class="np_cal">
			<a href="<?php echo CAL_XHTML_Url($this->data['nav']['prev_link']);?>" title="<?php echo CAL_getResource('PREV_CALENDAR_TITLE');?>"><?php echo CAL_getResource('PREV_CALENDAR');?></a>
		</th>
		<th<?php if ($this->data['width'] > 0) echo ' colspan="'.$this->data['width'].'"';?>>
		<?php echo CAL_getResource($this->data['nav']['title']['weekday']);?>, <?php echo CAL_getResource($this->data['nav']['title']['month']);?> <?php echo $this->data['nav']['title']['day'];?>,  <?php echo $this->data['nav']['title']['year'];?>
		</th>
		<th class="np_cal">
			<a href="<?php echo CAL_XHTML_Url($this->data['nav']['next_link']);?>" title="<?php echo CAL_getResource('NEXT_CALENDAR_TITLE');?>"><?php echo CAL_getResource('NEXT_CALENDAR');?></a>
		</th>
	</tr>
		<?php
		$col_offset = array();
		for($i=0;$i<$this->data['width'];$i++) {
			$col_offset[$i] = 0;
		}
		foreach($this->data['body'] as $cHour => $data) {
		?>
		<tr class="hour_cal">
			<td class="htitle_cal">
				<?php
					if (isset($data['add'])) {
				?>
				<a href="<?php echo CAL_XHTML_Url($data['add']);?>" title="<?php echo CAL_getResource('add event');?>" <?php if ($this->calendar->getAddEventTarget()!='') { ?>target="<?php echo $this->calendar->getAddEventTarget(); ?>" <?php } ?>><?php echo KT_convertDate($cHour, 'YYYY-mm-dd HH:ii:ss', $time_format);?></a>
				<?php
					} else {
				?>
				<?php echo KT_convertDate($cHour, 'YYYY-mm-dd HH:ii:ss', $time_format);?>
				<?php
					}
				?>
			</td>
			<?php
			$atLeastOneTdRendered = false;
			for($i=0;$i<$this->data['width'];$i++) {
				for($j=0;$j<count($data['event']);$j++) {
					if ($data['event'][$j]['position'] == $i) {
						$atLeastOneTdRendered = true;
						$col_offset[$i] += $data['event'][$j]['length'];
			?>
				<td rowspan="<?php echo $data['event'][$j]['length'];?>" class="event_cal<?php if ($data['event'][$j]['class'] != '') echo " " . $data['event'][$j]['class']; ?>">
					<div class="htitle_cal">
					<?php echo KT_convertDate($data['event'][$j]['start'], 'YYYY-mm-dd HH:ii:ss', $time_format);?>
					<?php if ($this->calendar->getDisplayEndHour() && CAL_extract('H-i', $data['event'][$j]['start']) != CAL_extract('H-i', $data['event'][$j]['end'])) { ?>
						<?php echo ' - '.KT_convertDate($data['event'][$j]['end'], 'YYYY-mm-dd HH:ii:ss', $time_format);?>
					<?php }?>
					</div>
					<div>
					<a href="<?php echo CAL_XHTML_Url($data['event'][$j]['link']);?>" title="<?php echo $data['event'][$j]['desc'];?>" <?php if ($this->calendar->getViewEventTarget()!='') { ?>target="<?php echo $this->calendar->getViewEventTarget(); ?>" <?php }?> ><?php echo $data['event'][$j]['title'];?></a>
					</div>
				</td>
			<?php
						break;
					}
				}
				if ($col_offset[$i] == 0) {
					$atLeastOneTdRendered = true;
			?>
				<td>&nbsp;</td>
			<?php
				} else {
					$col_offset[$i]--;
				}
				
			}

			if (!$atLeastOneTdRendered && $this->data['width'] == 0) {
			?>
				<td>&nbsp;</td>
			<?php
			}
			?>
			<td class="htitle_cal">&nbsp;</td>
		</tr>
		<?php
		}
		?>
</table>
<?php
	}
}
?>