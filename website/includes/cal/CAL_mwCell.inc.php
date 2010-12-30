	<td class="none_cal<?php if (isset($data['selected'])) echo " selected_cal";?><?php if (isset($data['today'])) echo " today_cal";?><?php if ($data['othermonth']) echo " othermonth_cal";?><?php if (count($data['event']) > 0) echo " hasevent_cal";?><?php if ($data['weekend'] && $data['othermonth'] == false) echo " weekend_cal";?>">
		<div class="mw_top_cal">
			<div>
				<?php
					if (isset($data['add']) || count($data['event'])>0) {
				?>
					<a href="<?php echo  CAL_XHTML_Url($data['link']);?>" title="<?php echo CAL_getResource('VIEW_DAY');?>"><?php if ($view == 'week') echo CAL_getResource($data['weekday']) . ', ';?><?php echo CAL_getResource($data['month']);?> <?php echo CAL_getResource($data['day']);?></a>
				<?php
					} else {
				?>
					<?php if ($view == 'week') echo CAL_getResource($data['weekday']) . ', ';?><?php echo CAL_getResource($data['month']);?> <?php echo CAL_getResource($data['day']);?>
				<?php
					}
				?>
			</div>
			<?php
			if (isset($data['add'])) {
			?>
			<a href="<?php echo  CAL_XHTML_Url($data['add']);?>" title="<?php echo CAL_getResource('add event');?>" <?php if ($this->calendar->getAddEventTarget()!='') { ?>target="<?php echo $this->calendar->getAddEventTarget(); ?>" <?php } ?>><?php echo CAL_getResource('ADD_NEW_EVENT');?></a>
			<?php
			}
			?>
			&nbsp;
		</div>
		<?php
			for ($i=0;$i<min(count($data['event']),$this->calendar->getMaxEvents());$i++) {
		?>
		<div class="event_cal<?php if ($data['event'][$i]['class'] != '') echo " " . $data['event'][$i]['class']; ?>">
			<div class="htitle_cal">
				<?php echo KT_convertDate($data['event'][$i]['start'], 'yyyy-mm-dd HH:ii:ss', $time_format);?>
				<?php
					if ($this->calendar->getDisplayEndHour() == true && CAL_extract('H-i', $data['event'][$i]['start']) != CAL_extract('H-i', $data['event'][$i]['end'])) {
				?>
					-
				<?php echo KT_convertDate($data['event'][$i]['end'], 'yyyy-mm-dd HH:ii:ss', $time_format);?>
				<?php
					}
				?>
			</div>
			<div><a href="<?php echo  CAL_XHTML_Url($data['event'][$i]['link']);?>" title="<?php echo $data['event'][$i]['desc'];?>" <?php if ($this->calendar->getViewEventTarget()!='') { ?>target="<?php echo $this->calendar->getViewEventTarget(); ?>" <?php } ?>><?php echo $data['event'][$i]['title'];?></a></div>
		</div>
		<?php
			}
		?>
		<?php
		if (count($data['event']) > $this->calendar->getMaxEvents()) {
		?>
		<div class="seemore_cal">
			<a href="<?php echo  CAL_XHTML_Url($data['link']);?>" title="<?php echo CAL_getResource('VIEW_DAY');?>"><?php echo CAL_getResource('AL_SEE_MORE_EVENTS');?></a>
		</div>
		<?php
		}
		?>
	</td>
