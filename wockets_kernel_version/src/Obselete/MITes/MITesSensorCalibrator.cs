using System;
using HousenCS.MITes;

namespace HousenCS.MITes
{
	/// <summary>
	/// Summary description for MITesSensorCalibrator.
	/// </summary>
	public class MITesSensorCalibrator
	{
		private MITesDecoder aMITesDecoder;

		private int[] lastAccelDataTime = new int[MITesData.MAX_MITES_CHANNELS];
		private bool[] foundAccelThisCheck = new bool[MITesData.MAX_MITES_CHANNELS];
		private int lastHRDataTime = 0;
		private bool isComputingNoise = false; 

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
        //public int GetLastSamplingRateComputed()
        //{
        //    return aMITesDecoder.GetLastSamplingRateComputed ();
        //}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesDecoder"></param>
		public MITesSensorCalibrator(MITesDecoder aMITesDecoder)
		{
			this.aMITesDecoder = aMITesDecoder;
			ResetDataCounts();
		}

		private void ResetDataCounts()
		{
			for (int i = 0; i < MITesData.MAX_MITES_CHANNELS; i++)
				numDataCounts[i] = 0;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public bool GetIsComputingNoise()
		{
			return isComputingNoise; 
		}
/// <summary>
/// 
/// </summary>
/// <param name="aValue"></param>
		public void SetIsComputingNoise(bool aValue)
		{
			isComputingNoise = aValue;
		}

		private double[,] means = new double[MITesData.MAX_MITES_CHANNELS,3];
		private double[,] sds = new double[MITesData.MAX_MITES_CHANNELS,3];

		private void ClearData()
		{
			for(int i = 0; i < MITesData.MAX_MITES_CHANNELS; i++)
				for (int j = 0; j < 3; j++)
				{
					means[i,j] = 0.0;
					sds[i,j] = 0.0;
				}
		}

		/// <summary>
		/// 
		/// </summary>
		public void ResetNoise()
		{
			for (int i = 0; i < numDataCounts.Length; i++)
				numDataCounts[i] = 0;
		}

		/// <summary>
		/// 
		/// </summary>
		public void DoNoiseComputation()
		{
			isComputingNoise = false;
			ClearData();
			double v; 

			//Compute sums
			for (int i = 0; i < MITesData.MAX_MITES_CHANNELS; i++)
				for (int j = 0; j < numDataCounts[i]; j++)
					for (int k = 0; k < 3; k++)
						means[i,k] += noiseData[i, j, k];

			//Divide by number of examples
			for (int i = 0; i < MITesData.MAX_MITES_CHANNELS; i++)
				if (numDataCounts[i]>0)
					for (int k = 0; k < 3; k++)
						means[i,k] /= numDataCounts[i];
			
			//Compute SD sum
			for (int i = 0; i < MITesData.MAX_MITES_CHANNELS; i++)
				for (int j = 0; j < numDataCounts[i]; j++)
					for (int k = 0; k < 3; k++)
					{
						v = noiseData[i, j, k];
						sds[i,k] += (v - means[i,k])*(v - means[i,k]);
					}

			//Divide by number of examples 
			for (int i = 0; i < MITesData.MAX_MITES_CHANNELS; i++)
				if (numDataCounts[i]>0)
					for (int k = 0; k < 3; k++)
					{
						sds[i,k] /= (numDataCounts[i]);
						//sds[i,k] = Math.Sqrt (sds[i,k]);
					}
			
			Console.WriteLine(GetNoiseDataString());
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public String GetNoiseDataString()
		{
			String str = "";
			for (int i = 0; i < MITesData.MAX_MITES_CHANNELS; i++)
				if (numDataCounts[i]>0)
				{
					str += "Means: " + Math.Round(means[i,0],3) + " " + Math.Round(means[i,1],3) + " " + Math.Round(means[i,2],3);
					str += "\r\nVARs : " + Math.Round(sds[i,0],3) + " " + Math.Round(sds[i,1],3) + " " + Math.Round(sds[i,2],3);
					str += "\r\n";
				}
			return str;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public String GetNoiseDataStringCSV()
		{
			String str = "";
			for (int i = 0; i < MITesData.MAX_MITES_CHANNELS; i++)
				if (numDataCounts[i]>0)
				{
					double m1 = Math.Round(means[i,0],3);
					double m2 = Math.Round(means[i,1],3);
					double m3 = Math.Round(means[i,2],3);
					double v1 = Math.Round(sds[i,0],3);
					double v2 = Math.Round(sds[i,1],3);
					double v3 = Math.Round(sds[i,2],3);
					str += "" + m1 + "," + m2 + "," + m3 + "," + (m1+m2+m3);
					str += "," + v1 + "," + v2 + "," + v3 + "," + (v1+v2+v3);
				}
			return str;
		}
		static int NUM_VALS_NOISE_COMP = 100;
		int[] numDataCounts = new int[MITesData.MAX_MITES_CHANNELS];
	    int[,,] noiseData = new int[MITesData.MAX_MITES_CHANNELS,NUM_VALS_NOISE_COMP,3];

		private int[,] histogram = new int[MITesData.MAX_MITES_CHANNELS,MITesData.NUM_ACCEL_STEPS];

		/// <summary>
		/// 
		/// </summary>
		public void ResetHist()
		{
			for (int j = 0; j < MITesData.MAX_MITES_CHANNELS; j++)
				for (int i = 0; i < MITesData.NUM_ACCEL_STEPS; i++)
					histogram[j,i] = 0; 
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="channel"></param>
		/// <param name="start"></param>
		/// <param name="end"></param>
		public void PrintHistogram(int channel, int start, int end)
		{
			for (int i = start; i < end; i++)
				Console.WriteLine (i + ": " + histogram[channel,i]);
		}

		/// <summary>
		/// 
		/// </summary>
		public void UpdateHist()
		{
			for (int i = 0; i < aMITesDecoder.someMITesDataIndex; i++)
			{
				if (aMITesDecoder.someMITesData[i].type == (int) MITesTypes.ACCEL)
				{
					int c = aMITesDecoder.someMITesData[i].channel;
					int v = aMITesDecoder.someMITesData[i].x;
					histogram[c,v] += 1;
				}
			}
		}
		
		private int histCount = 0; 

		/// <summary>
		/// 
		/// </summary>
		/// <param name="reportAfterCount"></param>
		/// <param name="channel"></param>
		/// <param name="start"></param>
		/// <param name="end"></param>
		public void ReportHist(int reportAfterCount, int channel, int start, int end)
		{
			if (histCount > reportAfterCount)
			{
				UpdateHist();
				PrintHistogram(channel, start, end);				
				histCount = 0;
			}
			else
			{
				UpdateHist();
				histCount += aMITesDecoder.someMITesDataIndex;
			}
		}

		int noiseCount = 0; 

		/// <summary>
		/// 
		/// </summary>
		public void ComputeNoise()
		{
			for (int i = 0; i < aMITesDecoder.someMITesDataIndex; i++)
			{
				if (aMITesDecoder.someMITesData[i].type == (int) MITesTypes.ACCEL)
				{
					noiseCount++; 
					channel = aMITesDecoder.someMITesData[i].channel;

					if (numDataCounts[channel] < NUM_VALS_NOISE_COMP)
					{
						noiseData[channel, numDataCounts[channel], 0] = aMITesDecoder.someMITesData[i].x;
						noiseData[channel, numDataCounts[channel], 1] = aMITesDecoder.someMITesData[i].y;
						noiseData[channel, numDataCounts[channel], 2] = aMITesDecoder.someMITesData[i].z;
						numDataCounts[channel] += 1;
					}
					else
					{
						// Filled one channel so stop
						isComputingNoise = false;
					}
				}
			}
		}

		private int channel; 
		private int time; 

		/// <summary>
		/// 
		/// </summary>
		public void UpdateSensorCalibrator()
		{
			if (isComputingNoise)
				ComputeNoise();

			for (int i = 0; i < MITesData.MAX_MITES_CHANNELS; i++)
				foundAccelThisCheck[i] = false;

			time = Environment.TickCount; //Slow operation. Call once. 
			for (int i = 0; i < aMITesDecoder.someMITesDataIndex; i++)
			{
				if (aMITesDecoder.someMITesData[i].type == (int) MITesTypes.ACCEL)
				{
					channel = aMITesDecoder.someMITesData[i].channel;
					if (!foundAccelThisCheck[channel])
					{
						foundAccelThisCheck[channel] = true;
						lastAccelDataTime[channel] = time;
					}
				}
				else if (aMITesDecoder.someMITesData[i].type == (int) MITesTypes.HR)
				{
					lastHRDataTime = time;
				}
			}
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public String GetStatusLine()
		{
			String str = "Sensor IDs seen in last 3s: ";
			for (int i = 0; i < MITesData.MAX_MITES_CHANNELS; i++)
				if (IsAccelData(i,3000))
					str += i + " ";
			if (IsHRData(3000))
				str += "HR";
			return str;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="channel"></param>
		/// <param name="withinTimeMS"></param>
		/// <returns></returns>
		public bool IsAccelData(int channel, int withinTimeMS)
		{
			if ((Environment.TickCount - lastAccelDataTime[channel]) < withinTimeMS)
				return true;
			else
				return false;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="withinTimeMS"></param>
		/// <returns></returns>
		public bool IsHRData(int withinTimeMS)
		{
			if ((Environment.TickCount - lastHRDataTime) < withinTimeMS)
				return true;
			else
				return false;
		}
	}
}
