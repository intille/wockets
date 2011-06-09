using System;
using HousenCS.IO;
using HousenCS.MITes;

namespace HousenCS.MITes
{
	/// <summary>
	/// A MITesLoggerReader reads the binary file saved by a MITesLogger and
	/// can replace an aMITesDecoder.GetSensorData(mrc) call. 
	/// </summary>
	public class MITesLoggerReaderNew
	{
		private ByteReader br;		
		private MITesDecoder aMITesDecoder;
 
		static int MAX_BYTES = 5*30; 
		byte[] someBytes = new byte[MAX_BYTES];  

		/// <summary>
		/// Initialize an object that will read raw binary data saved by a MITesLoggerNew.
		/// </summary>
		/// <param name="aMITesDecoder">MITesDecoder object</param>
		/// <param name="aByteFileName">String path for the binary file</param>
		public MITesLoggerReaderNew(MITesDecoder aMITesDecoder, String aByteFileName)
		{
			this.aMITesDecoder = aMITesDecoder;
			SetupFiles(aByteFileName);
		}

		private void SetupFiles(String pathName)
		{			
			br = new ByteReader(pathName);
			br.OpenFile();
		}	

		private static int[] ts = new int[1];
		private static byte[] b = new byte[1];
		private static int lastTime = 0; 
		private static double lastUnixTime = 0;
		private static bool readValid = true;
	
		private static byte[] b6 = new byte[6];

		/// <summary>
		/// 
		/// </summary>
		/// <param name="br"></param>
		/// <returns></returns>
		public static int ReadTimeStamp(ByteReader br)
		{
			//Console.WriteLine ("Read time stamp");
			readValid = br.ReadByte(b);

			if (!readValid)
			{
				return MITesData.NONE;
			}

			if (b[0] == ((int) 255))
			{
				//Console.WriteLine ("Marker");
				// Marker, so read the whole timecode
					br.ReadInt (ts);
					lastTime = ts[0];
					//Console.WriteLine ("Timecode: " + lastTime);
			}
			else
			{
				// Read only the difference between this and previous time (less than 255 ms)
				lastTime += (int) b[0];
				//Console.WriteLine ("Diff byte: " + b[0] + " modified Timecode: " + lastTime);
			}
			return lastTime;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="br"></param>
		/// <returns></returns>
		public static double ReadUnixTimeStamp(ByteReader br)
		{
			//Console.WriteLine ("Read UNIX time stamp");
			readValid = br.ReadByte(b);

			if (!readValid)
			{
				return MITesData.NONE;
			}

			if (b[0] == ((int) 255))
			{
				//Console.WriteLine ("Marker");
				// Marker, so read the whole timecode
				br.ReadBytes(b6);
				lastUnixTime = UnixTime.DecodeUnixTimeCodeBytes(b6);
				//Console.WriteLine ("UNIX Timecode: " + lastUnixTime);
			}
			else
			{
				// Read only the difference between this and previous time (less than 255 ms)
				lastUnixTime += (int) b[0];
				//Console.WriteLine ("Diff byte: " + b[0] + " modified UNIX Timecode: " + lastUnixTime);
			}
			return lastUnixTime;
		}

		static byte[] temp = new byte[1];
		int someMITesDataIndex;
		
		/// <summary>
		/// Grab sensor data from the saved MITesLogger binary file and use a MITesDecoder to decode it. 
		/// </summary>
		/// <param name="numPackets">The number of MITes packets to get</param>
		/// <param name="isPLFormat">True if PLFormat, false if older version.</param>
		public void GetSensorData(int numPackets, bool isPLFormat)
		{
			someMITesDataIndex = 0; 
			aMITesDecoder.someMITesDataIndex = aMITesDecoder.DecodeMITesLoggerData(numPackets, aMITesDecoder.someMITesData, someMITesDataIndex, br, isPLFormat);
		}

		private void ShutdownFiles()
		{
			br.CloseFile();
		}
	}
}