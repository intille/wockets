using System;
using HousenCS.IO;

namespace HousenCS.MITes
{
	/// <summary>
	/// An object that processes incoming MITes data and computes accelerometer activity counts for a given 
	/// epoch length. 
	/// </summary>
	public class MITesActivityCounter
	{
		private static bool DEBUG = false;
		private int ID = MITesData.NO_VALUE;
		private MITesDecoder aMITesDecoder;
		private double[] lastEpochVal = new double[3];
		private double lastEpochValAll = 0;

		private int[] lastVal = new int[3];
		private int lastValAll = 0;
		private double dx,dy,dz;
		private double[] diffSum = new double[3];
		private int diffSumCount = 0; 
		private double epochStartTime = 0;

        /// <summary>
        /// ANything above this value must be noise
        /// </summary>
	    public const int NOISE_CUTOFF = 100;

        /// <summary>
        /// Need at least this many samples to compute mean for any epoch length 
        /// </summary>
	    public const int SAMPLE_COUNT = 5; 

		/// <summary>
		/// Constructor for a MITesActivityCounter object, which computes acitivity counts for accelerometers.
		/// </summary>
		/// <param name="aMITesDecoder">The current MITesDecoder from which data will be pulled.</param>
		/// <param name="channel">The channel ID.</param>
		public MITesActivityCounter(MITesDecoder aMITesDecoder, int channel)
		{
			this.aMITesDecoder = aMITesDecoder;
			this.ID = channel; 
			ResetMaxMin();
		}
	
		/// <summary>
		/// Return the ID (or channel number) for the acceleromter used by this MITesActivityCounter.
		/// </summary>
		/// <returns>The int ID (channel number).</returns>
		public int GetID()
		{
			return ID;
		}

		private void Debug(String aMsg)
		{
			if (DEBUG)
				Console.WriteLine("DEBUG: " + aMsg);
		}

		private void Warning(String aMsg)
		{
			Console.WriteLine("WARNING: " + aMsg);
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public String GetReportKey()
		{
			String s = ",MITes " + ID + ":dx,MITes " + ID + ":dy,MITes " + ID + ":dz,MITes " + ID + ":all";
			return s;
		}

		/// <summary>
		/// 
		/// </summary>
		public void ComputeEpoch()
		{
			lastEpochVal[0] = GetEpochValueX();
			lastEpochVal[1] = GetEpochValueY();
			lastEpochVal[2] = GetEpochValueZ();
			lastEpochValAll = lastEpochVal[0] + lastEpochVal[1] + lastEpochVal[2];
			diffSumCount = 0;
		}

		private double GetEpochValueX()
		{
			double temp;
            if (diffSumCount >= SAMPLE_COUNT)
				temp = diffSum[0]/((double) diffSumCount);
			else 
				temp = 0;
			diffSum[0] = 0;

            if (temp > NOISE_CUTOFF)
            {
                Console.WriteLine("WARNING: NOISE CUTOFF IN Activity Counter");
                    temp = 0;
            } 
			return temp;
		}

		private double GetEpochValueY()
		{
			double temp;
            if (diffSumCount >= SAMPLE_COUNT)
				temp = diffSum[1]/((double) diffSumCount);
			else 
				temp = 0;
			diffSum[1] = 0;

            if (temp > NOISE_CUTOFF)
            {
                Console.WriteLine("WARNING: NOISE CUTOFF IN Activity Counter");
                temp = 0;
            } 

            return temp;
		}

		private double GetEpochValueZ()
		{
			double temp;
			if (diffSumCount >= SAMPLE_COUNT)
				temp = diffSum[2]/((double) diffSumCount);
			else 
				temp = 0;
			diffSum[2] = 0;

            if (temp > NOISE_CUTOFF)
            {
                Console.WriteLine("WARNING: NOISE CUTOFF IN Activity Counter");
                temp = 0;
            } 
            
            return temp;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public double GetLastEpochValueX()
		{
			return lastEpochVal[0]; 
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public double GetLastEpochValueY()
		{
			return lastEpochVal[1]; 
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public double GetLastEpochValueZ()
		{
			return lastEpochVal[2]; 
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public double GetLastEpochValueAll()
		{
			return lastEpochValAll; 
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public String GetReport(double aTime)
		{
		    epochStartTime = aTime;
            
			double x = GetLastEpochValueX();
			double y = GetLastEpochValueY();
			double z = GetLastEpochValueZ();
			double all = GetLastEpochValueAll();

			String s = "";
			if (x != 0)
			{
				s += ", " + Math.Round (x,2);
			}
			else
				s += "," + MITesActivityLogger.NONE_STRING;

			if (y != 0)
				s += ", " + Math.Round (y,2);
			else
				s += "," + MITesActivityLogger.NONE_STRING;

			if (z != 0)
				s += ", " + Math.Round (z,2);
			else
				s += "," + MITesActivityLogger.NONE_STRING;

			if (all != 0)
				s += ", " + Math.Round (all,2);
			else
				s += "," + MITesActivityLogger.NONE_STRING;

			return s;
		}

        public static String GetEmptyReport()
        {
            String s = "";
            s += "," + MITesActivityLogger.NONE_STRING;
            s += "," + MITesActivityLogger.NONE_STRING;
            s += "," + MITesActivityLogger.NONE_STRING;
            s += "," + MITesActivityLogger.NONE_STRING;

            return s;
        }

        /// <summary>
        /// 
        /// </summary>
        /// <returns></returns>


        /// <summary>
        /// 
        /// </summary>
        /// <returns></returns>
        public String GetReport()
        {
            return GetReport(Environment.TickCount);
        }

        
        /// <summary>
		/// Given new data, update the activity counts. This should appear in the main
		/// loop of code that is processing the data. 
		/// </summary>
		public void UpdateActivityCounts()
		{
			for (int i = 0; i < aMITesDecoder.someMITesDataIndex; i++)
			{
				if (aMITesDecoder.someMITesData[i].type == (int) MITesTypes.ACCEL)
				{
					if (aMITesDecoder.someMITesData[i].channel == ID)
					{
						DiffAndSetLastAccel(
							aMITesDecoder.someMITesData[i].channel,
							aMITesDecoder.someMITesData[i].x,
							aMITesDecoder.someMITesData[i].y,
							aMITesDecoder.someMITesData[i].z);
						SetMaxMin(
							aMITesDecoder.someMITesData[i].channel,
							aMITesDecoder.someMITesData[i].x,
							aMITesDecoder.someMITesData[i].y,
							aMITesDecoder.someMITesData[i].z);			
					}
				}
			}
		}

		private void DiffAndSetLastAccel(int id, int x, int y, int z)
		{
			if ((lastVal[0] != MITesData.EMPTY) && (x != MITesData.EMPTY))
				dx = Math.Abs (x-lastVal[0]);
			else 
				dx = 0;
			
			if ((lastVal[1] != MITesData.EMPTY) && (x != MITesData.EMPTY))
				dy = Math.Abs (y-lastVal[1]);
			else 
				dy = 0;

			if ((lastVal[2] != MITesData.EMPTY) && (x != MITesData.EMPTY))
				dz = Math.Abs (z-lastVal[2]);
			else 
				dz = 0;

//			Debug("ID: " + id + 
//				" x: " + x + " " + lastVal[id,0] + "(" + dx + ")" +
//				" y: " + y + " " + lastVal[id,1] + "(" + dy + ")" +
//				" z: " + z + " " + lastVal[id,2] + "(" + dz + ")");

			diffSum[0] += dx;
			diffSum[1] += dy;
			diffSum[2] += dz;
			diffSumCount++; 

			lastVal[0] = x;
			lastVal[1] = y;
			lastVal[2] = z;

			lastValAll = 0;
			if ((x == MITesData.EMPTY) && 
				(y == MITesData.EMPTY) &&
				(z == MITesData.EMPTY))
				lastValAll = MITesData.NO_VALUE;
			else
			{
				if (x != MITesData.EMPTY)
					lastValAll += x;
				if (y != MITesData.EMPTY)
					lastValAll += y;
				if (z != MITesData.EMPTY)
					lastValAll += z;
			}
		}
		
		int minx, miny, minz;
		int maxx, maxy, maxz;

		private void ResetMaxMin()
		{
			minx = 1025;
			miny = 1025;
			minz = 1025;
			maxx = -1;
			maxy = -1;
			maxz = -1;
		}

		private int maxMinTime = 0;
		/// <summary>
		/// 
		/// </summary>
		public void PrintMaxMin()
		{
			if ((Environment.TickCount-maxMinTime)> 5000)
			{
				if (maxx <= MITesData.NUM_ACCEL_STEPS)
				{
					Console.WriteLine ("ID: " + ID + " Min: " + minx + " " + miny + " " + minz + " Max: " + maxx + " " + maxy + " " + maxz);
				}
				ResetMaxMin();
				maxMinTime = Environment.TickCount;
			}
		}

		private void SetMaxMin(int id, int x, int y, int z)
		{
			if (x < minx)
				minx = x;
			if (y < miny)
				miny = y;
			if (z < minz)
				minz = z;
			if (x > maxx)
				maxx = x;
			if (y > maxy)
				maxy = y;
			if (z > maxz)
				maxz = z;
		}
		
		//		private int vx,vy,vz;
//		private bool meanValue(int index, double[] someMeans)
//		{
//			double sum = 0.0;
//			double sumx = 0.0;
//			double sumy = 0.0;
//			double sumz = 0.0; 
//
//			// Check if no data
//			if (activityCountsIndex[index] == 0)
//				return false;
//
//			// Some data, so take mean
//			for (int i = 0; i < activityCountsIndex[index]; i++)
//			{
//				vx = activityCounts[index,i,0];
//				vy = activityCounts[index,i,1];
//				vz = activityCounts[index,i,2];
//				
//				sumx += vx;
//				sumy += vy;
//				sumz += vz;
//				sum += vx + vy + vz; 
//			}
//
//			sum = sum/((double) activityCountsIndex[index]);
//			sumx = sumx/((double) activityCountsIndex[index]);
//			sumy = sumy/((double) activityCountsIndex[index]);
//			sumz = sumz/((double) activityCountsIndex[index]);
//
//			// Reset
//			activityCountsIndex[index] = 0;
//
//			//			double vsum = 0;
//			//			double d = 0;
//			//			for (int i = 0; i < activityCountsIndex[index]; i++)
//			//			{
//			//				d = activityCounts[index,i] - sum;
//			//				vsum += d*d;
//			//			}
//			//			vsum = vsum / activityCountsIndex[index];			
//			//			vsum = Math.Sqrt (vsum);
//	
//			Debug("Sum: " + sum + "(" + sumx + "," + sumy + " " + sumz + ")");
//			//sum = gaussWeight(sum);
//			//Console.WriteLine ("WSum: " + sum);
//			//Console.WriteLine ("ID: " + index + " " + sum + " " + vsum + " (" + activityCountsIndex[index] + ")");
//			
//			someMeans[0] = sum;
//			someMeans[1] = sumx;
//			someMeans[2] = sumy;
//			someMeans[3] = sumz;
//			return true;
//		}

		/// <summary>
		/// Returns true if the given time less that the epoch time.
		/// </summary>
        /// <param name="currentTime">A time in milliseconds</param>
        /// <param name="epochTimeLen">A time in milliseconds</param>
        /// <returns>True if ATime is less than epochTimeLen</returns>
		public bool IsNewEpoch(double currentTime, int epochTimeLen)
		{
			if ((currentTime-epochStartTime) > epochTimeLen)
				return true;
			else
				return false;
		}

        /// <summary>
        /// Returns true if epochTimeLen has not elapsed since EpochStartTime.
        /// </summary>
        /// <param name="epochTimeLen">A time in milliseconds</param>
        /// <returns>True if ATime is less than epochTime</returns>
        public bool IsNewEpoch(int epochTimeLen)
        {
            return IsNewEpoch(Environment.TickCount, epochTimeLen); 
        }
        
        /// <summary>
		/// Return the epochTime being used. 
		/// </summary>
		/// <returns>A time in milliseconds</returns>
		public double GetLastEpochTime()
		{
			return epochStartTime;
		}
	}
}
