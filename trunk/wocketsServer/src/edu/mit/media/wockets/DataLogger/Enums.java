package edu.mit.media.wockets.DataLogger;

public class Enums {
	
	public static enum DATA_TYPE{
		PROMPTING,PHONE_STATS,SWAPPING,WOCKET_STATS,NOVALUE ;
		
		public static DATA_TYPE toData_Type(String str)
	    {
		       try {
		            return valueOf(str);
		        } 
		        catch (Exception ex) {
		            return NOVALUE;
		        }
	    }
	};
	
	public static enum PROMPT{
		Participant_Id,Prompt_Type,prompt_Time,Response_Time,Activity_Interval,
		Primary_Activity,Alternate_Activities,NOVALUE;
		
		public static PROMPT toPROMPT(String str)
	    {
		       try {
		            return valueOf(str);
		        } 
		        catch (Exception ex) {
		            return NOVALUE;
		        }
	    }
	}
	
	public static enum PHONESTATS{
		Participant_Id,Create_Date,Phone_Battery,Main_Memory,SD_Memory,NOVALUE;
		
		public static PHONESTATS toPHONESTATS(String str)
	    {
		       try {
		            return valueOf(str);
		        } 
		        catch (Exception ex) {
		            return NOVALUE;
		        }
	    }
		
	}
	
	public static enum SWAPPING{
		Participant_Id,Swap_Time,Swap_Event,Restarted_Event,LocationChanged_Event,
		Mac_Id,Sensor_Placement,NOVALUE;
		
		public static SWAPPING toSwapping(String str)
	    {
		       try {
		            return valueOf(str);
		        } 
		        catch (Exception ex) {
		            return NOVALUE;
		        }
	    }
	}
	
	public static enum WOCKETSTATS{
		Participant_Id,Mac_Id,Create_Date,Activity_Count,Wocket_Battery,Transmitted_Byte,
		Received_Bytes,NOVALUE;
		
		public static WOCKETSTATS toWocketStats(String str)
	    {
		       try {
		            return valueOf(str);
		        } 
		        catch (Exception ex) {
		            return NOVALUE;
		        }
	    }
		
	}
	

}
