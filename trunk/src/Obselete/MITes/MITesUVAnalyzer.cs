using System;

namespace HousenCS.MITes
{
	/// <summary>
	/// Summary description for MITesActivityCounter.
	/// </summary>
	public class MITesUVAnalyzer
	{
		private static int MAX_LIGHT_STORED = 30; 
		private int[] lightVals = new int[MAX_LIGHT_STORED];
		private int lightValsIndex = 0; 
		private int lastTime = 0; 

		/// <summary>
		/// 
		/// </summary>
		public static int NO_VALUE = -1;

        /// <summary>
        /// Specify that data from any ID for UV sensor should be used 
        /// </summary>
        public static int NONE = -1;

		private int ID = 0; 

		private MITesDecoder aMITesDecoder;

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesDecoder"></param>
		/// <param name="anID"></param>
		public MITesUVAnalyzer(MITesDecoder aMITesDecoder, int anID)
		{
			this.ID = anID; 
			this.aMITesDecoder = aMITesDecoder;
			ResetLightVals();
		}

		private void Warning(String aMsg)
		{
			Console.WriteLine("WARNING: " + aMsg);
		}

		private void AddLightValue(int aLightValue)
		{
			lightValsIndex++;
			if (lightValsIndex == MAX_LIGHT_STORED)
				lightValsIndex = 0;

			lightVals[lightValsIndex] = aLightValue;
		}

//		public double GetVarianceLightValue()
//		{
//			double mean = GetMeanLightValue(); 
//			double var = 0.0;
//			int count = 0; 
//			for (int i = 0; i < lightVals.Length; i++)
//			{
//				if (lightVals[i] != NO_VALUE)
//				{
//					count++;
//					var += (lightVals[i] - mean)*(lightVals[i] - mean);
//				}
//			}
//			if (count != 0)
//				var /= ((double) count);
//			else 
//				var = NO_VALUE; 
//			return var;
//		}
//
//		public double GetSDLightValue()
//		{
//			double mean = GetMeanLightValue(); 
//			double var = GetVarianceLightValue();
//			if (var == NO_VALUE)
//				return NO_VALUE;
//			else
//				return Math.Sqrt(var);
//		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public double GetMeanLightValue()
		{
			double mean = 0.0; 
			int count = 0; 
			for (int i = 0; i < lightVals.Length; i++)
			{
				if (lightVals[i] != NO_VALUE)
				{
					count++;
					mean += lightVals[i];
				}
			}
			if (count != 0)
				mean /= ((double) count);
			else
				mean = NO_VALUE;
			return mean;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public int GetLastLightValue()
		{
			if ((Environment.TickCount-lastTime)<1000)
				return lightVals[lightValsIndex];
			else
				return NO_VALUE; 
		}

		/// <summary>
		/// 
		/// </summary>
		public void GetRecentLightVals()
		{
			for (int i = 0; i < aMITesDecoder.someMITesDataIndex; i++)
			{
			    if (aMITesDecoder.someMITesData[i].type == (int) MITesTypes.UV)
			    {
			        if ((ID == NONE) ||
                        (aMITesDecoder.someMITesData[i].id == ID))
			        {
			            if ((Environment.TickCount - lastTime) > 1000)
			            {
			                AddLightValue(aMITesDecoder.someMITesData[i].sensorValue);
			                lastTime = Environment.TickCount;
			                //Console.WriteLine("UV ID: " + aMITesDecoder.someMITesData[i].id);
			            }
			        }
			    }
			}
			if ((Environment.TickCount-lastTime)>2000)
			{
				lastTime = Environment.TickCount; 
				AddLightValue(NO_VALUE);
			}
		}

		private void ResetLightVals()
		{
			for (int i = 0; i < MAX_LIGHT_STORED; i++)
				lightVals[i] = NO_VALUE; 
			lightValsIndex = 0; 
		}
	}
}