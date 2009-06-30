using System;

namespace HousenCS.MITes
{
	/// <summary>
	/// Summary description for MITesActivityCounter.
	/// </summary>
	public class MITesRangeAnalyzer
	{
		//private double maxDist = 0; 
		private const int MAX_SAMP_PER_SEC = 36;
		private const int MAX_EPOCH_TIME_MS = 60000;
		private int epochTimeMS = 5000; // Default 5s
		private int lastEpochValue = MITesData.NO_VALUE;

		private int[] history;
		private int[] historyTimes;
		int lastDist; 
		
		/// <summary>
		/// 
		/// </summary>
		public static int NO_VALUE = -1;
		private int lastTime = 0; 
		private int ID = 0;

		private MITesDecoder aMITesDecoder;

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public int GetID()
		{
			return ID;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aTimeMS"></param>
		public void SetEpochTimeMS(int aTimeMS)
		{
			if (aTimeMS > MAX_EPOCH_TIME_MS)
			{
				Warning("SetEpochTimeMS for MITesRangeAnalyzer too large. Setting to " + MAX_EPOCH_TIME_MS);
				epochTimeMS = MAX_EPOCH_TIME_MS;
			}
			else
				epochTimeMS = aTimeMS; 
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public String GetReportKey()
		{
			String s = ",Min dist ID " + ID + " epoch " + epochTimeMS + "ms";
			return s;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public String GetReport()
		{
			int min = GetEpochValue();
			String s;
			if (min != NO_VALUE)
				s = ", " + min;
			else
				s = "," + MITesActivityLogger.NONE_STRING;
			return s;
		}

		/// <summary>
		/// 
		/// </summary>
		public void ComputeEpoch()
		{			
			lastEpochValue = ComputeEpochValue(); 
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public int GetEpochValue()
		{
			return lastEpochValue;
		}

		private int ComputeEpochValue()
		{
			int min = 4;
			int count = 0;
			int time = Environment.TickCount;
			for (int i = 0; i < history.Length; i++)
				if (((time-historyTimes[i]) < epochTimeMS) &&
					(history[i] != NO_VALUE))
				{
					count++;
					//Console.WriteLine ("Time: " + (time-historyTimes[i]));
					if (history[i] < min)
					{
						min = history[i];
						//						if (min == 0)
						//							return 0; // Best result, return immediately
					}
				}
			//Console.WriteLine ("Count (" + epochTimeMS + "): " + count);
			if (min == 4)
				return NO_VALUE;
			else
				return min;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesDecoder"></param>
		/// <param name="ID"></param>
		public MITesRangeAnalyzer(MITesDecoder aMITesDecoder, int ID)
		{
			history = new int[(int) Math.Ceiling((double) MAX_SAMP_PER_SEC*(MAX_EPOCH_TIME_MS/1000))];
			historyTimes = new int[history.Length];
			ResetDistVals();

			this.aMITesDecoder = aMITesDecoder;
			this.ID = ID; 
		}

		private void Warning(String aMsg)
		{
			Console.WriteLine("WARNING: " + aMsg);
		}

//		private void AddDistance(int aDistance)
//		{
//			//Console.WriteLine (aDistance);
//			distValsIndex++; 
//			if (distValsIndex == MAX_DIST_STORED)
//				distValsIndex = 0;
//
//			distVals[distValsIndex] = aDistance;
//		}

		private void AddDistance(int aDistance, int aTime)
		{
			for (int i = 0; i < history.Length; i++)
				if ((aTime-historyTimes[i]) > MAX_EPOCH_TIME_MS)
				{
					//Console.WriteLine ("Added to loc: " + i);
					history[i] = aDistance;
					historyTimes[i] = aTime;
					lastDist = aDistance;
					//Console.WriteLine (aDistance + " at " + i);
					return;
				}
			Console.WriteLine ("ERROR: ran out of space in RangeAnalyzer array");
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public int GetLastDistance()
		{
			if ((Environment.TickCount-lastTime)<1000)
				return lastDist;
			else
				return NO_VALUE;
		}

//		int max = 0; 
//		
//		/// <summary>
//		/// 
//		/// </summary>
//		/// <returns></returns>
//		public int GetMaxDistance()
//		{
//			max = NO_VALUE;
//			for (int i = 0; i < MAX_DIST_STORED; i++)
//			{
//				if (distVals[i]>=max)
//					max = distVals[i];
//			}
//			return max;
//		}
//

//		private int min = 0; 
//	
//		/// <summary>
//		/// 
//		/// </summary>
//		/// <returns></returns>
//		public int GetMinDistance()
//		{
//			min = 4;
//			for (int i = 0; i < MAX_DIST_STORED; i++)
//			{
//				if ((distVals[i]<min) && (distVals[i] != NO_VALUE))
//					min = distVals[i];
//			}
//			if (min == 4)
//				min = NO_VALUE;
//			return min;
//		}

		/// <summary>
		/// 
		/// </summary>
		public void UpdateDistanceVals()
		{
			for (int i = 0; i < aMITesDecoder.someMITesDataIndex; i++)
			{
				if (aMITesDecoder.someMITesData[i].type == (int) MITesTypes.RANGE)
				{
					Console.WriteLine ("Range ID: " + aMITesDecoder.someMITesData[i].id);
					if (aMITesDecoder.someMITesData[i].id == ID)
					{
						//Console.WriteLine ("Add: " + aMITesDecoder.someMITesData[i].sensorValue + " " + aMITesDecoder.someMITesData[i].timeStamp);
						lastTime = aMITesDecoder.someMITesData[i].timeStamp;
						AddDistance(aMITesDecoder.someMITesData[i].sensorValue, lastTime);
					}
				}
			}
//			// Enter a No_VALUE if no value in last second
//			if ((Environment.TickCount-lastTime)>1000)	
//				AddDistance(NO_VALUE, Environment.TickCount);
		}

		private void ResetDistVals()
		{
			for (int i = 0; i < history.Length; i++)
			{
				history[i] = NO_VALUE;
				historyTimes[i] = 0;
			} 
		}
	}
}