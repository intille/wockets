using System;

namespace HousenCS.MITes
{
	/// <summary>
	/// Summary description for MITesActivityCounter.
	/// </summary>
	public class MITesHRAnalyzer
	{
		private int meanTimeMS = 30000; // Default to 30 seconds
		private int lastReportTime = 0;
		private short ID = (short) MITesData.NONE; 
		private short lastID = (short) MITesData.NONE;
		private short lastHR = 0;
		private int lastHRTime = 0;
		private MITesDecoder aMITesDecoder;
		private double lastMeanHR;
		private short[] hrVals = new short[60];
		private int[] hrValTimes = new int[60];

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public int GetMeanTimeMS()
		{
			return meanTimeMS;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public String GetReportKey()
		{
			String s;
			if (lastID == MITesData.NONE)
				s = ",HR,HR mean over " + meanTimeMS + "ms";
			else
				s = ", HR " + lastID + ", HR " + lastID + " mean over " + meanTimeMS + "ms";
			return s;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public String GetReport()
		{
			String str; 
			if (IsNewHR(lastReportTime))
			{
				str = "," + GetLastHR();
				lastReportTime = GetLastTime();
			}
			else
				str = "," + MITesActivityLogger.NONE_STRING;
 
			if (GetLastMean() == 0)
				str = str + "," + MITesActivityLogger.NONE_STRING;
			else
				str	= str + "," + Math.Round(GetLastMean(),2);
	
			return str; 
		}



		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesDecoder"></param>
		/// <param name="anID"></param>
		public MITesHRAnalyzer(MITesDecoder aMITesDecoder, int anID)
		{
			this.ID = (short) anID; 
			this.aMITesDecoder = aMITesDecoder;

			for (int i = 0; i < hrVals.Length; i++)
			{
				hrVals[i] = 0;
				hrValTimes[i] = 0;
			}
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesDecoder"></param>
		public MITesHRAnalyzer(MITesDecoder aMITesDecoder): this(aMITesDecoder, MITesData.NONE)
		{
		}

		private void Warning(String aMsg)
		{
			Console.WriteLine("WARNING: " + aMsg);
		}

		/// <summary>
		/// Check if HR value is in a reasonable range for a normal or well-conditioned person: 40-200.
		/// </summary>
		/// <param name="hrVal">A heart rate value</param>
		/// <returns>True if a reasonable heart rate</returns>
		public bool InReasonableRange(int hrVal)
		{	
			if (hrVal <= 40)
				return false;
			else if (hrVal >= 250)
				return false;
			else
				return true;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aTimeIntervalMS"></param>
		/// <returns></returns>
		public int GetRecentHR(int aTimeIntervalMS)
		{
			if ((Environment.TickCount-lastHRTime) < aTimeIntervalMS)
				return lastHR;
			else
				return MITesData.NONE; 
		}

		private int lastValidHR = 0; 
		/// <summary>
		/// 
		/// </summary>
		public short Update()
		{
			for (int i = 0; i < aMITesDecoder.someMITesDataIndex; i++)
			{
				if (aMITesDecoder.someMITesData[i].type == (int) MITesTypes.HR)
				{
					if ((ID == MITesData.NONE) ||
						(ID == aMITesDecoder.someMITesData[i].id))
					{
						if (InReasonableRange(aMITesDecoder.someMITesData[i].sensorValue))
						{
							lastHRTime = aMITesDecoder.someMITesData[i].timeStamp;
                            MITesDataFilterer.MITesPerformanceTracker[0].SampleCounter = MITesDataFilterer.MITesPerformanceTracker[0].SampleCounter + 1;
							if ((lastHRTime - lastValidHR) > 200)
							{
								lastHR = (short) aMITesDecoder.someMITesData[i].sensorValue;
								lastValidHR = lastHRTime;
								Console.WriteLine ("HR:: " + lastHR);
								AddHR(lastHR, lastHRTime, meanTimeMS); 
								lastID = aMITesDecoder.someMITesData[i].id;

                                return lastHR;
                                
							}
						}
					}
				}
			}

            return -1;
		}


        /// <summary>
        /// 
        /// </summary>
        public short UpdateOffline()
        {
            for (int i = 0; i < aMITesDecoder.someMITesDataIndex; i++)
            {
                if (aMITesDecoder.someMITesData[i].type == (int)MITesTypes.HR)
                {
                    if ((ID == MITesData.NONE) ||
                        (ID == aMITesDecoder.someMITesData[i].id))
                    {
                        if (InReasonableRange(aMITesDecoder.someMITesData[i].sensorValue))
                        {
                            lastHRTime = aMITesDecoder.someMITesData[i].timeStamp;                            
                            if ((lastHRTime - lastValidHR) > 200)
                            {
                                lastHR = (short)aMITesDecoder.someMITesData[i].sensorValue;                      
                                Console.WriteLine("HR:: " + lastHR);
                                AddHR(lastHR, lastHRTime, meanTimeMS);
                                lastID = aMITesDecoder.someMITesData[i].id;
                                return lastHR;

                            }
                            lastValidHR = lastHRTime;
                        }
                    }
                }
            }

            return -1;
        }

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public int GetLastTime()
		{
			return lastHRTime; 
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aTime"></param>
		/// <returns></returns>
		public bool IsNewHR(int aTime)
		{
			if (aTime < lastHRTime)
				return true;
			else
				return false;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public int GetLastHR()
		{
			return lastHR;
		}

		private int GetOpenHRSlot(int aTimeMS, int aveTimeMS)
		{
			int index = 0;
			bool isFound = false;
			while ((!isFound) && (index < hrVals.Length))
			{
				if ((aTimeMS - hrValTimes[index]) > aveTimeMS)
					return index;
				index++;
			}
			Console.WriteLine ("ERROR in GetOpenHRSlot");
			return 0;
		}

		int j; 
		private void AddHR(short hrVal, int hrTime, int aveTimeMS)
		{
			j = GetOpenHRSlot(hrTime, aveTimeMS);
			hrVals[j] = hrVal;
			hrValTimes[j] = hrTime;
		}

		private void MeanHR(int aTimeMS, int aveTimeMS)
		{
			meanTimeMS = aveTimeMS;
			int sum = 0;
			int count = 0;
			for (int i = 0; i < hrVals.Length; i++)
			{
				if ((aTimeMS - hrValTimes[i]) <= aveTimeMS)
				{
					sum += hrVals[i];
					count++;
				}
			}
			if (count != 0)
			{
				lastMeanHR = (sum / ((double) count));
			}
			else
				lastMeanHR = 0.0;
		}


		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public double GetLastMean()
		{
			return lastMeanHR;
		}	


		/// <summary>
		/// 
		/// </summary>
		/// <param name="timeToAvg"></param>
		public void ComputeEpoch(int timeToAvg)
		{
			MeanHR(Environment.TickCount,  timeToAvg);
		}
	}
}
