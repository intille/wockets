package edu.mit.media.wockets.DataLogger;

import java.util.List;

import com.ibm.icu.text.SimpleDateFormat;

import edu.mit.media.wockets.DataLogger.DataLoggerBean.PhoneStats;
import edu.mit.media.wockets.DataLogger.DataLoggerBean.Prompting;
import edu.mit.media.wockets.DataLogger.DataLoggerBean.Swapping;
import edu.mit.media.wockets.DataLogger.DataLoggerBean.WocketStats;

public class UpdateDataContainer {
	
	public static SimpleDateFormat DATETIMEFORMAT = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss");
	
	public void updateDataContainerGSON(DataContainer dataContainer)
	{
		List<PhoneStats> phoneStatsList = dataContainer.getPhoneStatsList();
		List<Prompting> promptingList = dataContainer.getPromptingList();
		List<WocketStats> wocketStatsList = dataContainer.getWocketStateList();
		List<Swapping> swappingList = dataContainer.getSwappingList();
		
		updatePhoneStats(phoneStatsList);
		updatePrompt(promptingList);
		updateWocketStats(wocketStatsList);
		updateSwapping(swappingList);
	}
	
	public void updatePhoneStats(List<PhoneStats> phoneStatsList)
	{
		if(phoneStatsList != null)
		{
		for(PhoneStats ps: phoneStatsList)
			ps.setCreateDate(DATETIMEFORMAT.format(ps.getDateTime().getTime()));
		}
	}
	
	public void updatePrompt(List<Prompting> promptingList)
	{
		if(promptingList !=null)
		{
			for(Prompting pr: promptingList)
			{
				pr.setPromptTime(DATETIMEFORMAT.format(pr.getpTime().getTime()));
				pr.setResponseTime(pr.getrTime()!=null ? DATETIMEFORMAT.format(pr.getrTime()):null);
			}
		}
	}
	
	public void updateWocketStats(List<WocketStats> wocketStatsList)
	{
		if(wocketStatsList != null)
		{
			for(WocketStats ws: wocketStatsList)
				ws.setCreateDate(DATETIMEFORMAT.format(ws.getDateTime().getTime()));
		}
	}
	
	public void updateSwapping(List<Swapping> swappingList)
	{
		if(swappingList != null)
		{
			for(Swapping sw: swappingList)
			{
				sw.setSwapTime(DATETIMEFORMAT.format(sw.getDateTime().getTime()));
				sw.setSwapEvent(sw.isSwap() == true ? "1":"0");
				sw.setRestartedEvent(sw.isRestarted() == true ? "1":"0");
				sw.setLoctChangedevent(sw.isLocationChange() == true ? "1":"0");
			}
		}
	}

}
