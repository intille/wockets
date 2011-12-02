/**
 * Created By Salim Khan
 * Act as a handler when event occure during XML parsing
 */
package edu.mit.media.wockets.DataLogger;

import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

import edu.mit.media.wockets.DataLogger.Enums.PHONESTATS;
import edu.mit.media.wockets.DataLogger.DataLoggerBean.*;

public class SAXHandler extends DefaultHandler {
	
	private DataContainer dataContainer;//containes all Wockets log data in the form of list
	private String tempStr;
	private int tempInt;
	private char tempChar;
	private Enums.DATA_TYPE tempDATA_TYPE;
	//Wocket Data temp beans
	private Prompting prompt;
	private PhoneStats phoneStat;
	private SwappedSensor swappedSensor;
	private Swapping swapping;
	private WocketStats wocketStats;
	

	public SAXHandler(DataContainer dataContainer)
	{
		this.dataContainer = dataContainer;
	}
	
	//call at start of any xml tag
	public void startElement(String uri, String localName, String qName,Attributes attributes)
							throws SAXException
	{
		System.out.println(qName);
		//create new temp object based on qName string
		switch(Enums.DATA_TYPE.toData_Type(qName))
		{
			case PROMPTING:
				//prompt = new Prompting();
				tempDATA_TYPE = Enums.DATA_TYPE.toData_Type(qName);//store start tag into temp
				break;
			case PHONE_STATS:
				//phoneStat = new PhoneStats();
				tempDATA_TYPE = Enums.DATA_TYPE.toData_Type(qName);
				break;
			case WOCKET_STATS:
				//wocketStats = new WocketStats();
				tempDATA_TYPE = Enums.DATA_TYPE.toData_Type(qName);
				break;
			case SWAPPING:
				//swapping = new Swapping();
				//swappedSensor = new SwappedSensor();
				tempDATA_TYPE = Enums.DATA_TYPE.toData_Type(qName);
				break;
			case NOVALUE:
				//nothing 
			default:
				//nothing
		}
		
		//for each row
		if(qName.equals("row"))
		{
			switch(tempDATA_TYPE)
			{
				case PROMPTING:
					prompt = new Prompting();
					break;
				case PHONE_STATS:
					phoneStat = new PhoneStats();
					break;
				case WOCKET_STATS:
					wocketStats = new WocketStats();
					break;
				case SWAPPING:
					swapping = new Swapping();
					//swappedSensor = new SwappedSensor();
					break;
				case NOVALUE:
					//nothing 
				default:
					//nothing
			}
		}
		
		if(qName.equals("Swapped_Sensor"))
		{
			swappedSensor = new SwappedSensor();
			swappedSensor.setMacId(attributes.getValue("Mac_Id"));
		}
	}
	
	//runs all characters between tags
	public void characters(char[] ch, int start, int length)
	{
		tempStr = new String(ch,start,length);
		System.out.println(tempStr);
	}
	
	//runs when end of tag
	public void endElement(String uri, String localName,String qName)
	{
		System.out.println(qName);
//		switch(Enums.DATA_TYPE.toData_Type(qName))
//		{
//			case PROMPTING:
//				dataContainer.getPromptingList().add(prompt);//add prompt object to data container
//				//prompt = null;
//				break;
//			case PHONE_STATS:
//				dataContainer.getPhoneStatsList().add(phoneStat);
//				phoneStat = null;
//				break;
//			case WOCKET_STATS:
//				dataContainer.getWocketStateList().add(wocketStats);
//				wocketStats = null;
//				break;
//			case SWAPPING:
//				dataContainer.getSwappingList().add(swapping);//set Swapping temp obj to data container
//				dataContainer.getSwappedSensorList().add(swappedSensor);//set swappedSensor to data container
//				swapping = null;
//				swappedSensor = null;
//				break;
//			case NOVALUE:
//				setValue(qName, tempStr);
//		}
		if(qName.equals("row"))
		{
			switch(tempDATA_TYPE)
			{
				case PROMPTING:
					dataContainer.getPromptingList().add(prompt);//add prompt object to data container
					prompt = null;
					break;
				case PHONE_STATS:
					dataContainer.getPhoneStatsList().add(phoneStat);
					phoneStat = null;
					break;
				case WOCKET_STATS:
					dataContainer.getWocketStateList().add(wocketStats);
					wocketStats = null;
					break;
				case SWAPPING:
					//swapping.setSwappedSensor(swappedSensor);
					//swapping.getSwappedSensor().add(swappedSensor);
					dataContainer.getSwappingList().add(swapping);//set Swapping temp obj to data container
					dataContainer.getSwappedSensorList().add(swappedSensor);//set swappedSensor to data container
					swapping = null;
					swappedSensor = null;
					break;
				case NOVALUE:
					//nothing 
				default:
					//nothing
			}
			
		}
		else if(qName.equals("Swapped_Sensor"))
		{
			swappedSensor.setSensorPlacement(tempStr);
			swapping.getSwappedSensor().add(swappedSensor);
		}
		else 
			setValue(qName, tempStr);
}
	
	
	//utilities methods for setting data in temp bean
	public void setValue(String endTag, String tempStr)
	{
		switch(tempDATA_TYPE)
		{
			case PROMPTING:
				setValueOfPrompt(endTag,tempStr);
				break;
			case PHONE_STATS:
				setValueOfPhoneStat(endTag, tempStr);
				break;
			case WOCKET_STATS:
				setValueOfWocketStat(endTag, tempStr);
				break;
			case SWAPPING:
				setValueOfSwapping(endTag, tempStr);
				break;
			default:
				//nothing
		}
	}
	
	public void setValueOfPrompt(String endTag, String tempStr)
	{
		switch(Enums.PROMPT.toPROMPT(endTag))
		{
			case Participant_Id:
				prompt.setParticipantId(Integer.parseInt(tempStr));
				break;
			case Prompt_Type:
				prompt.setPromptType(tempStr);
				break;
			case prompt_Time:
				prompt.setPromptTime(tempStr.replaceAll("T"," "));
				break;
			case Response_Time:
				if(tempStr!=null)
					prompt.setResponseTime(tempStr.replaceAll("T"," "));
				break;
			case Activity_Interval:
				prompt.setActivityInterval(Integer.parseInt(tempStr));
				break;
			case Primary_Activity:
				prompt.setPrimaryActivity(tempStr);
				break;
			case Alternate_Activities:
				prompt.setAlternateActivity(tempStr);
				break;
			default:
				//nothing
		}
	}
	
	
	public void setValueOfPhoneStat(String endTag, String tempStr)
	{
		switch(Enums.PHONESTATS.toPHONESTATS(endTag))
		{
			case Participant_Id:
				phoneStat.setParticipantId(Integer.parseInt(tempStr));
				break;
			case Create_Date:
				phoneStat.setCreateDate(tempStr.replaceAll("T", " "));
				break;
			case Phone_Battery:
				phoneStat.setPhoneBattery(Integer.parseInt(tempStr));
				break;
			case Main_Memory:
				phoneStat.setMainMemo(Integer.parseInt(tempStr));
				break;
			case SD_Memory:
				phoneStat.setSdMemo(Integer.parseInt(tempStr));
				break;
			default:
				//nothing
			
		}
	}
	
	public void setValueOfSwapping(String endTag, String tempStr)
	{
		switch(Enums.SWAPPING.toSwapping(endTag))
		{
			case Participant_Id:
				swapping.setParticipantId(Integer.parseInt(tempStr));
				break;
			case Swap_Time:
				swapping.setSwapTime(tempStr.replaceAll("T", " "));
				break;
			case Swap_Event:
				swapping.setSwapEvent(tempStr);
				break;
			case Restarted_Event:
				swapping.setRestartedEvent(tempStr);
				break;
			case LocationChanged_Event:
				swapping.setLoctChangedevent(tempStr);
				break;
			//for SWAPPED_SENSOR Table
//			case Mac_Id:
//				swappedSensor.setMacId(tempStr);
//				break;
//			case Sensor_Placement:
//				swappedSensor.setSensorPlacement(tempStr);
//				break;
			default:
				//nothing
		}
	}
	
	public void setValueOfWocketStat(String endTag, String tempStr)
	{
		switch(Enums.WOCKETSTATS.toWocketStats(endTag))
		{
			case Participant_Id:
				wocketStats.setParticipantId(Integer.parseInt(tempStr));
				break;
			case Mac_Id:
				wocketStats.setMacId(tempStr);
				break;
			case Create_Date:
				wocketStats.setCreateDate(tempStr.replaceAll("T"," "));
				break;
			case Activity_Count:
				wocketStats.setActivityCount(Integer.parseInt(tempStr));
				break;
			case Wocket_Battery:
				wocketStats.setWocketBattery(Integer.parseInt(tempStr));
				break;
			case Transmitted_Byte:
				wocketStats.setTransmittedByte(Integer.parseInt(tempStr));
				break;
			default:
				//nothing
		}
	}

}
