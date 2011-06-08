using System;
using System.ComponentModel;
using System.Runtime.InteropServices;
using System.Threading;

namespace HousenCS.MITes
{
	/// <summary>
	/// An object that grabs a SystemTime that appears to be accurate to about 5ms (as compared
	/// with Environment.TickCount, which is accurate only to about 200ms). Makes a native call
	/// to QueryPerformanceCounter. 
	/// </summary>
	public class MITesSystemTime
	{

		[DllImport("CoreDll.dll")]
		static extern int QueryPerformanceFrequency(ref long lpFrequency);

		[DllImport("CoreDll.dll")]
		static extern int QueryPerformanceCounter(ref long lpPerformanceCount);


		private static long val = 0;
		private static long freq = 0;
		private static double msScale = 1.0;

		/// <summary>
		/// Create the object and initialize the frequency value. 
		/// </summary>
		static MITesSystemTime()
		{
			QueryPerformanceFrequency(ref freq);
			msScale = (1.0/freq)*1000.0;
			Console.WriteLine ("MITesSystemTime minimum resolution is " + (1/freq) + " seconds.");
		}

		/// <summary>
		/// Get the frequency at which the MITesSystemTime can work.
		/// </summary>
		/// <returns>A long frequency value</returns>
		public static long GetFrequency()
		{
			return freq;
		}

		/// <summary>
		/// From a time difference between two calls to GetTime, compute the time that has
		/// elapsed in seconds. 
		/// </summary>
		/// <param name="aTimeDiff">The diffrence between two calls to GetTime.</param>
		/// <returns>A time in seconds.</returns>
		public static double GetDuration(long aTimeDiff)
		{
			return aTimeDiff/((double)freq);
		}
	
		/// <summary>
		/// Return a system time that is in milliseconds that is accurate to 1 ms.
		/// </summary>
		/// <returns>A system time in milliseconds</returns>
		public static long GetSystemTimeMS()
		{
			return (long) Math.Floor(GetTime()*msScale);
		}

		/// <summary>
		/// Get a system time that is accurate to less than 1 ms.
		/// </summary>
		/// <returns>A long system time value</returns>
		public static long GetTime()
		{
			QueryPerformanceCounter(ref val);
			return val;
		}

		/// <summary>
		/// 
		/// </summary>
		public void TestTimecode()
		{
			long v1, v2;
			v1 = MITesSystemTime.GetSystemTimeMS ();
			Thread.Sleep (1000);
			v2 = MITesSystemTime.GetSystemTimeMS ();
			Console.WriteLine("================= " + " Diff: " + (v2-v1) + " Duration: " + MITesSystemTime.GetDuration(v2-v1));
			Console.WriteLine ("Frequency: " + MITesSystemTime.GetFrequency());

			for (int i = 0; i < 10000; i++)
			{
				//Console.WriteLine(i + " Tickcount: " + Environment.TickCount);
				//v2 = Environment.TickCount;
				v2 = MITesSystemTime.GetSystemTimeMS();
				//v2 = DateTime.Now.Ticks;
				Console.WriteLine(i + " Diff: " + (v2-v1) + " Duration: " + MITesSystemTime.GetDuration(v2-v1));
				Thread.Sleep(5);
				v1 = v2;
			}
		}
	}
}