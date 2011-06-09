using System;
using System.Runtime.InteropServices;

namespace HousenCS.MITes
{
	/// <summary>
	/// Summary description for UnixTime.
	/// </summary>
	public class UnixTime
	{
		/// <summary>
		/// 
		/// </summary>
		public static DateTime UnixRef = new DateTime(1970,1,1,0,0,0,0);

        /// <summary>
		/// 
		/// </summary>
		public static DateTime UnixRefNoUTC = new DateTime(1970,1,1,0,0,0,0);

		/// <summary>
		/// 
		/// </summary>
		public static double MilliInDay = 86400000;
		/// <summary>
		/// 
		/// </summary>
		public static double MilliInHour = 3600000;

		/// <summary>
		/// 
		/// </summary>
		/// <param name="unixTime"></param>
		/// <param name="dt"></param>
		public static void GetDateTime(long unixTime, out DateTime dt)
		{
			dt = UnixRefNoUTC.AddMilliseconds(unixTime);			
		}

        /// <summary>
        /// 
        /// </summary>
        /// <param name="unixTime"></param>
        /// <param name="aDate"></param>
        /// <returns></returns>
        public static int IntTimeFromUnixTime(double unixTime, DateTime aDate)
        {
            double tmp = unixTime - GetUnixTime(aDate); 
            if (tmp > Int32.MaxValue)
                Console.WriteLine("ERROR IN conversion UnixTime to int time");
            return ((int) tmp); 
        }

		/// <summary>
		/// 
		/// </summary>
		/// <param name="dt"></param>
		/// <returns></returns>
		public static double GetUnixTime(DateTime dt)
		{
			TimeSpan ts = dt.ToUniversalTime().Subtract(UnixRef);
			return  ts.TotalMilliseconds;
		
		}

#if (PocketPC)
        [DllImport("CoreDll.dll")]
#else
        [DllImport("kernel32.dll")]        
#endif

        private static extern bool QueryPerformanceCounter(
            out long lpPerformanceCount);
        

#if (PocketPC)
        [DllImport("CoreDll.dll")]
#else
        [DllImport("kernel32.dll")]
#endif
        private static extern bool QueryPerformanceFrequency(
             out long lpFrequency);

        private static System.Int64 counter = 0;
        private static System.Int64 referenceCounter = 0;
        private static System.Int64 freq = 0;
        private static double referenceTime;
        private static double max_previous_time = 0;
        private static double current_time = 0;
        private static Random RandomClass = new Random();
       // private static int expectedSampleSpacing;
        

        public static void InitializeTime()
        {
            //get the performance counter frequency only once
            QueryPerformanceFrequency(out freq);
            referenceTime = ((TimeSpan)(DateTime.Now.Subtract(UnixRef))).TotalMilliseconds;
            //DateTime dt=(new DateTime(1970, 1, 1, 0, 0, 0)).AddMilliseconds(referenceTime);
            QueryPerformanceCounter(out referenceCounter);
            //UnixTime.expectedSampleSpacing = (int) Math.Floor((double)expectedSampleSpacing);
        }

        /// <summary>
        /// 
        /// </summary>
        /// <returns></returns>
        public static double GetUnixTime()
        {
            QueryPerformanceCounter(out counter);
            current_time = (double)(referenceTime + ((counter - referenceCounter) * 1000.0 / (double)freq));

            double diff = current_time - previousTime;

            if (diff <= 1)
            {
                previousTime++;
                return previousTime;
            }
            
                
            previousTime = current_time;
            
            return current_time;            
        }
		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
        /// 
        //static double[] times = new double[1000];
        //static double[] times2 = new double[1000];
        //static int c1 = 0;
        //static double current_time_dt;

        private static double previousTime=0;
        private static double[] previousTimes = new double[MITesDecoder.MAX_CHANNEL];

		public static double GetUnixTime(int channel)
		{
            QueryPerformanceCounter(out counter);
            current_time = (double)(referenceTime + ((counter - referenceCounter) * 1000.0 / (double)freq)); //(double) DateTime.Now.Ticks; //((TimeSpan)(DateTime.UtcNow.Subtract(UnixRef))).TotalMilliseconds;            

            int diff = (int)(current_time - previousTimes[channel]);
            if (diff <= 0)
                current_time = previousTimes[channel] + 1;
            previousTimes[channel] = current_time;          
            //if (sensor_id == 0) //HR
                return current_time;
           //else //ACCEL
           // {
           //     if ((long)current_time > (long) MITesDataFilterer.MITesPerformanceTracker[sensor_id].LastTimeStamp)
           //     {
           //         MITesDataFilterer.MITesPerformanceTracker[sensor_id].LastTimeStamp=current_time;
           //         return current_time;
           //     }else
           //     {
           //         current_time=MITesDataFilterer.MITesPerformanceTracker[sensor_id].LastTimeStamp+
           //             (1000/MITesDataFilterer.MITesPerformanceTracker[sensor_id].PerfectRate);
           //         MITesDataFilterer.MITesPerformanceTracker[sensor_id].LastTimeStamp = current_time;
           //         return current_time;
           //     }
           // }

            //if (current_time > max_previous_time)
            //    max_previous_time = current_time;
           // else
           //     max_previous_time = max_previous_time + 1;// (1000 / expectedSamplingRate);
    

           // return max_previous_time;

            //current_time_dt = ((TimeSpan)(DateTime.UtcNow.Subtract(UnixRef))).TotalMilliseconds;
            //times2[c1] = current_time_dt;
            //times[c1++] = current_time;
            //c1 = c1 % 1000;


           //c1 = c1 % 1000;
           //// return current_time;

           //if (current_time > max_previous_time)          
           //    max_previous_time = current_time;
           //else           
           //    max_previous_time = max_previous_time + 1;

           // return max_previous_time;
		
		}

        
		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public static TimeSpan GetUnixTimeSpan()
		{
			return ((TimeSpan)(DateTime.UtcNow.Subtract(UnixRef)));

		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="unixTime"></param>
		/// <returns></returns>
		public static int GetUnixTimeSecond(double unixTime)
		{
			try
			{
				return Convert.ToInt32(Math.Floor(unixTime/1000));
			}
			catch(Exception e)
			{
                e.ToString();
				//Console.Out.WriteLine("Error: UnixTime: GetUnixTimeSec: "+e.ToString());
				return 0;
			}
			
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="unixTime"></param>
		/// <returns></returns>
		public static short GetUnixTimeMSecond(double unixTime)
		{
			try
			{
				return Convert.ToInt16(Math.Round(unixTime%1000));
			}
			catch(Exception e)
			{
                e.ToString();
				//Console.Out.WriteLine("Error: UnixTime: GetUnixTimeSec: "+e.ToString());
				return 0;
			}	
		
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="unixTime"></param>
		/// <param name="retBytes"></param>
		public static void GetUnixTimeBytesOld(double unixTime, byte[] retBytes)
		{
//			ushort ms = UnixTime.GetUnixTimeMSecond(unixTime);
//			uint sec = UnixTime.GetUnixTimeSecond(unixTime);
//			byte[] temp;
//			temp = System.BitConverter.GetBytes(sec);
//	
//			retBytes[5]=temp[0];
//			retBytes[4]=temp[1];
//			retBytes[3]=temp[2];
//			retBytes[2]=temp[3];
//
//			temp = System.BitConverter.GetBytes(ms);
//				
//			retBytes[1] = temp[0];
//			retBytes[0] = temp[1];			
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="unixTime"></param>
		/// <param name="retBytes"></param>
		public static void GetUnixTimeBytes(double unixTime, byte[] retBytes)
		{
			if (BitConverter.IsLittleEndian == false)
				Console.WriteLine ("ERROR: assumes littleendian!");

			short ms = UnixTime.GetUnixTimeMSecond(unixTime);
			int sec = UnixTime.GetUnixTimeSecond(unixTime);
			byte[] temp;
			temp = System.BitConverter.GetBytes(sec);
	
			retBytes[0]=temp[0];
			retBytes[1]=temp[1];
			retBytes[2]=temp[2];
			retBytes[3]=temp[3];

			temp = System.BitConverter.GetBytes(ms);
				
			retBytes[4] = temp[0];
			retBytes[5] = temp[1];			
		}

		private static byte[] temp2 = new byte[2];
		private static byte[] temp4 = new byte[4];
		

		/// <summary>
		/// 
		/// </summary>
		/// <param name="someBytes"></param>
		/// <returns>A timecode (based on UNIX time) in MS</returns>
		public static double DecodeUnixTimeCodeBytes(byte[] someBytes)
		{
			int sec = DecodeUnixTimeSecBytes(someBytes);
			short ms = DecodeUnixTimeMSBytes(someBytes);

			double ds = (double) sec;
			double dms = (double) ms;

			return ((ds*1000) + dms); 
		}

        /// <summary>
        /// Works SSI 
        /// </summary>
        /// <param name="someBytes"></param>
        /// <returns>A timecode (based on UNIX time) in MS</returns>
        public static double DecodeUnixTimeCodeBytesFixed(byte[] someBytes)
        {
            int sec = DecodeUnixTimeSecBytes(someBytes);
            int ms = (int)DecodeUnixTimeMSBytesLong(someBytes);

            double ds = (double)sec;
            double dms = (double)ms;

            return ((ds * 1000) + dms);
        }
        
        /// <summary>
		/// 
		/// </summary>
		/// <param name="someBytes"></param>
		/// <returns></returns>
		public static double DecodeUnixTimeCodeBytesOld(byte[] someBytes)
		{
//			uint sec = DecodeUnixTimeSecBytes(someBytes);
//			ushort ms = DecodeUnixTimeMSBytes(someBytes);
//
//			double ds = (double) sec;
//			double dms = (double) ms;
//
//			return ((ds*1000) + dms); 
			return 0;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="someBytes"></param>
		/// <returns></returns>
		public static int DecodeUnixTimeSecBytes(byte[] someBytes)
		{
			temp4[0] = someBytes[0];
			temp4[1] = someBytes[1];
			temp4[2] = someBytes[2];
			temp4[3] = someBytes[3];
			return System.BitConverter.ToInt32(temp4,0);
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="someBytes"></param>
		/// <returns></returns>
		public static short DecodeUnixTimeMSBytes(byte[] someBytes)
		{
			temp2[0] = someBytes[1]; 
			temp2[1] = someBytes[0];
			return System.BitConverter.ToInt16(temp2,0);
		}

        /// <summary>
        /// 
        /// </summary>
        /// <param name="someBytes"></param>
        /// <returns></returns>
        public static long DecodeUnixTimeMSBytesLong(byte[] someBytes)
        {
            temp4[0] = someBytes[4];
            temp4[1] = someBytes[5];
            temp4[2] = 0;
            temp4[3] = 0;
            return System.BitConverter.ToInt32(temp4, 0);
        }

		/// <summary>
		/// Returns bytes in format seconds[5-2][LSB-MSB] milliseconds[1-0][LSB-MSB]
		/// </summary>
		/// <param name="unixTime"></param>
		/// <returns></returns>
		public static byte[] GetUnixTimeBytes(double unixTime)
		{
			byte[] ret = new byte[6];
			GetUnixTimeBytes(unixTime, ret);
			return ret;
		}
	}
}
