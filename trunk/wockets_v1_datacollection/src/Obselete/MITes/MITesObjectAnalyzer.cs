using System;
using System.Collections;

namespace HousenCS.MITes
{
	/// <summary>
	/// Summary description for MITesActivityCounter.
	/// </summary>
	public class MITesObjectAnalyzer
	{
		private static int MAX_OBJECT_STORED = 60; // About 30 seconds of values
		private int[] objectVals = new int[MAX_OBJECT_STORED];
		private int[] objectValsTime = new int[MAX_OBJECT_STORED];
        private int[] objectValsVal = new int[MAX_OBJECT_STORED];
        private bool[] objectValsAlive = new bool[MAX_OBJECT_STORED];
        private int objectValsIndex = 0; 
		private int lastTime = 0; 
		private int ID = MITesData.NONE;
		private MITesDecoder aMITesDecoder;
		private int epochTimeMS = 0;
		private bool lastSeen = false;

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesDecoder"></param>
		/// <param name="anID">If ID is MITesData.NONE then use any object sensor, ignoring ID</param>
		public MITesObjectAnalyzer(MITesDecoder aMITesDecoder, int anID)
		{
			this.aMITesDecoder = aMITesDecoder;
			ResetObjectVals();
			this.ID = anID; 
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public String GetReportKey()
		{
			String s = ",last object " + ID + " val, object " + ID + " moved in " + epochTimeMS + "ms";
			return s;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public String GetReport()
		{
			String s = "";
			int lastVal = GetLastValue();

			if (lastVal != MITesData.NO_VALUE)
				s += ", " + lastVal;
			else
				s += "," + MITesActivityLogger.NONE_STRING;

			if (lastSeen)
				s += ", " + ID; 
			else
				s += "," + MITesActivityLogger.NONE_STRING;

			return s;
		}


		private void Warning(String aMsg)
		{
			Console.WriteLine("WARNING: " + aMsg);
		}

		private void AddObjectValue(int aObjectValue, int aTime, int aVal, bool isAlive)
		{
			objectValsIndex++;
			if (objectValsIndex == MAX_OBJECT_STORED)
				objectValsIndex = 0;
			objectVals[objectValsIndex] = aObjectValue;
			objectValsTime[objectValsIndex] = aTime;
            objectValsVal[objectValsIndex] = aVal;
            objectValsAlive[objectValsIndex] = isAlive;
        }

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public bool IsSeenEpoch()
		{
			return lastSeen;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aTimeWindowMS"></param>
		public void ComputeEpoch(int aTimeWindowMS)
		{
			epochTimeMS = aTimeWindowMS;
			ComputeIsSeenEpoch(Environment.TickCount, aTimeWindowMS);
		}

		private bool ComputeIsSeenEpoch(int aTime, int aTimeWindowMS)
		{
			bool isSeen = false;
			for (int i = 0; i < objectVals.Length; i++)
			{
				if ((objectVals[i] != MITesData.NO_VALUE) &&
					((aTime-objectValsTime[i]) < aTimeWindowMS))
				{
					if (objectVals[i] == ID)
						isSeen = true;
				}
			}
			lastSeen = isSeen;
			return isSeen;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public int GetLastValue()
		{
			if ((Environment.TickCount-objectValsTime[objectValsIndex])<1000)
				return objectVals[objectValsIndex];
 		    else
				return MITesData.NO_VALUE; 
		}

        private string GetIDString(int id, int val, bool isAlive)
        {
            string s = id.ToString();

            if (isAlive)
                s += "(alive)";
            else if (val == 0)
                s += "(stop)";
            return s;
        }

        /// <summary>
        /// Get IDs seen in the last bit of time. 
        /// </summary>
        /// <param name="aTimeInMS">Time in MS to look back.</param>
        /// <returns>A list of ID values as informative strings</returns>
        public ArrayList GetRecentIDs(int aTimeInMS)
        {
            ArrayList someIDs = new ArrayList();
            int tempTime = Environment.TickCount;
            // oldest to newest
            for (int i = objectValsIndex+1; i < objectVals.Length; i++)
            {
                if ((tempTime - objectValsTime[i]) < aTimeInMS)
                {
                    string s = GetIDString(objectVals[i], objectValsVal[i], objectValsAlive[i]); 
                    if (!someIDs.Contains(s))
                        someIDs.Add(s);  
                }
            }
            for (int i = 0; i <= objectValsIndex; i++)
            {
                if ((tempTime - objectValsTime[i]) < aTimeInMS)
                {
                    string s = GetIDString(objectVals[i], objectValsVal[i], objectValsAlive[i]);
                    if (!someIDs.Contains(s))
                        someIDs.Add(s);
                }
            }
            return someIDs; 
        }

	    /// <summary>
		/// Grab and store the latest object values from the MITesDecoder data stream.
		/// </summary>
		public void Update()
		{
			for (int i = 0; i < aMITesDecoder.someMITesDataIndex; i++)
			{
				if (aMITesDecoder.someMITesData[i].type == (int) MITesTypes.STATIC)
				{
					if ((ID == MITesData.NONE) ||
						(aMITesDecoder.someMITesData[i].id == ID))
					{
						lastTime = Environment.TickCount;
						Console.WriteLine("OBJECT: " + aMITesDecoder.someMITesData[i].sensorValue);
						AddObjectValue(aMITesDecoder.someMITesData[i].id, lastTime, aMITesDecoder.someMITesData[i].sensorValue, aMITesDecoder.someMITesData[i].isAlive);
					}
				}
			}
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public int GetID()
		{
			return ID;
		}

		private void ResetObjectVals()
		{
			for (int i = 0; i < objectVals.Length; i++)
			{
				objectVals[i] = MITesData.NO_VALUE;
				objectValsTime[i] = 0;
			}
			objectValsIndex = 0; 
		}
	}
}