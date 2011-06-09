using System;

namespace HousenCS.MITes
{
	/// <summary>
	/// Summary description for MITesActivityCounter.
	/// </summary>
	public class MITesTempAnalyzer
	{
		private static int MAX_TEMP_STORED = 60; // About 30 seconds of values
		private int[] tempVals = new int[MAX_TEMP_STORED];
		private int[] tempValsTime = new int[MAX_TEMP_STORED];
		private int tempValsIndex = 0; 
		private int lastTime = 0; 
		private int ID = MITesData.NONE;
		private MITesDecoder aMITesDecoder;
		private double lastVariance = 0;
		private double lastMean = 0;
		private int epochTimeMS = 0; 

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesDecoder"></param>
		/// <param name="anID">If ID is MITesData.NONE then use any temp sensor, ignoring ID</param>
		public MITesTempAnalyzer(MITesDecoder aMITesDecoder, int anID)
		{
			this.aMITesDecoder = aMITesDecoder;
			ResetTempVals();
			this.ID = anID; 
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public String GetReportKey()
		{
			String s = ",last temp " + ID + " val, temp " + ID + " mean of epoch " + epochTimeMS + "ms, " + "temp " + ID + " sd of epoch " + epochTimeMS + "ms";
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

			if (lastMean != MITesData.NO_VALUE)
				s += ", " + Math.Round(lastMean,2);
			else
				s += "," + MITesActivityLogger.NONE_STRING;

			if (lastVariance != MITesData.NO_VALUE)
				s += ", " + Math.Round(lastVariance,2);
			else
				s += "," + MITesActivityLogger.NONE_STRING;

			return s;
		}


		private void Warning(String aMsg)
		{
			Console.WriteLine("WARNING: " + aMsg);
		}

		private void AddTempValue(int aTempValue, int aTime)
		{
			tempValsIndex++;
			if (tempValsIndex == MAX_TEMP_STORED)
				tempValsIndex = 0;
			tempVals[tempValsIndex] = aTempValue;
			tempValsTime[tempValsIndex] = aTime; 
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public double GetEpochVariance()
		{
			return lastVariance;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public double GetEpochSD()
		{
			if (lastVariance == MITesData.NO_VALUE)
				return MITesData.NO_VALUE;
			else
				return Math.Sqrt(lastVariance);
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public double getEpochMean()
		{
			return lastMean;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aTimeWindowMS"></param>
		public void ComputeEpoch(int aTimeWindowMS)
		{
			epochTimeMS = aTimeWindowMS;
			ComputeEpochVariance(Environment.TickCount, aTimeWindowMS);
		}

		private void ComputeEpochVariance(int aTime, int aTimeWindowMS)
		{
			double mean = ComputeEpochMean(aTime, aTimeWindowMS); 
			double var = 0.0;
			int count = 0; 
			for (int i = 0; i < tempVals.Length; i++)
			{
				if ((tempVals[i] != MITesData.NO_VALUE) &&
					((aTime-tempValsTime[i]) < aTimeWindowMS))
				{
					count++;
					var += (tempVals[i] - mean)*(tempVals[i] - mean);
				}
			}
			if (count != 0)
				var /= ((double) count);
			else 
				var = MITesData.NO_VALUE;

			lastVariance = var;
		}

		private double ComputeEpochMean(int aTime, int aTimeWindowMS)
		{
			double mean = 0.0; 
			int count = 0; 
			for (int i = 0; i < tempVals.Length; i++)
			{
				if ((tempVals[i] != MITesData.NO_VALUE) &&
					((aTime-tempValsTime[i]) < aTimeWindowMS))
				{
					count++;
					mean += tempVals[i];
				}
			}
			if (count != 0)
				mean /= ((double) count);
			else
				mean = MITesData.NO_VALUE;

			lastMean = mean;
			return mean;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public int GetLastValue()
		{
			if ((Environment.TickCount-tempValsTime[tempValsIndex])<1000)
				return tempVals[tempValsIndex];
 		    else
				return MITesData.NO_VALUE; 
		}

		/// <summary>
		/// Grab and store the latest temp values from the MITesDecoder data stream.
		/// </summary>
		public void Update()
		{
			for (int i = 0; i < aMITesDecoder.someMITesDataIndex; i++)
			{
				if (aMITesDecoder.someMITesData[i].type == (int) MITesTypes.TEMP)
				{
					if ((ID == MITesData.NONE) ||
						(aMITesDecoder.someMITesData[i].id == ID))
					{
						lastTime = Environment.TickCount;
						AddTempValue(aMITesDecoder.someMITesData[i].sensorValue, lastTime);
					}
				}
			}
//			if ((Environment.TickCount-lastTime)>2000)
//			{
//				lastTime = Environment.TickCount; 
//				AddTempValue(NO_VALUE);
//			}
		}

		private void ResetTempVals()
		{
			for (int i = 0; i < tempVals.Length; i++)
			{
				tempVals[i] = MITesData.NO_VALUE;
				tempValsTime[i] = 0;
			}
			tempValsIndex = 0; 
		}
	}
}