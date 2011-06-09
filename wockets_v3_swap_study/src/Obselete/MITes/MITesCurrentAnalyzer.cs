using System;

namespace HousenCS.MITes
{
	/// <summary>
	/// Summary description for MITesActivityCounter.
	/// </summary>
	public class MITesCurrentAnalyzer
	{
		private static int MAX_CURRENT_STORED = 60; // About 30 seconds of values
		private int[] currentVals = new int[MAX_CURRENT_STORED];
		private int[] currentValsTime = new int[MAX_CURRENT_STORED];
		private int currentValsIndex = 0; 
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
		/// <param name="anID">If ID is MITesData.NONE then use any current sensor, ignoring ID</param>
		public MITesCurrentAnalyzer(MITesDecoder aMITesDecoder, int anID)
		{
			this.aMITesDecoder = aMITesDecoder;
			ResetCurrentVals();
			this.ID = anID; 
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public String GetReportKey()
		{
			String s = ",last current " + ID + " val, current " + ID + " mean of epoch " + epochTimeMS + "ms, " + "current " + ID + " sd of epoch " + epochTimeMS + "ms";
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

		private void AddCurrentValue(int aCurrentValue, int aTime)
		{
			currentValsIndex++;
			if (currentValsIndex == MAX_CURRENT_STORED)
				currentValsIndex = 0;
			currentVals[currentValsIndex] = aCurrentValue;
			currentValsTime[currentValsIndex] = aTime; 
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
			for (int i = 0; i < currentVals.Length; i++)
			{
				if ((currentVals[i] != MITesData.NO_VALUE) &&
					((aTime-currentValsTime[i]) < aTimeWindowMS))
				{
					count++;
					var += (currentVals[i] - mean)*(currentVals[i] - mean);
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
			for (int i = 0; i < currentVals.Length; i++)
			{
				if ((currentVals[i] != MITesData.NO_VALUE) &&
					((aTime-currentValsTime[i]) < aTimeWindowMS))
				{
					count++;
					mean += currentVals[i];
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
			if ((Environment.TickCount-currentValsTime[currentValsIndex])<1000)
				return currentVals[currentValsIndex];
 		    else
				return MITesData.NO_VALUE; 
		}

		/// <summary>
		/// Grab and store the latest current values from the MITesDecoder data stream.
		/// </summary>
		public void Update()
		{
			for (int i = 0; i < aMITesDecoder.someMITesDataIndex; i++)
			{
				if (aMITesDecoder.someMITesData[i].type == (int) MITesTypes.CURRENT)
				{
					if ((ID == MITesData.NONE) ||
						(aMITesDecoder.someMITesData[i].id == ID))
					{
						lastTime = Environment.TickCount;
						AddCurrentValue(aMITesDecoder.someMITesData[i].sensorValue, lastTime);
					}
				}
			}
//			if ((Environment.TickCount-lastTime)>2000)
//			{
//				lastTime = Environment.TickCount; 
//				AddCurrentValue(NO_VALUE);
//			}
		}

		private void ResetCurrentVals()
		{
			for (int i = 0; i < currentVals.Length; i++)
			{
				currentVals[i] = MITesData.NO_VALUE;
				currentValsTime[i] = 0;
			}
			currentValsIndex = 0; 
		}
	}
}