using System;
using System.Diagnostics;
using System.Threading;
using HousenCS.IO;
using HousenCS.MITes;

namespace HousenCS.MITes
{
	/// <summary>
	/// A MITesLoggerNew saves MITes data into binary and csv files for later use. 
	/// </summary>
	public class MITesLoggerNew
	{
		private ByteWriter bw;
		private ByteWriter bwPLFormat;
		private FileWriter fw; 
		private String fnData;
		private String fnDataPLFormat;
		private String logData;
		//private int timeCount = 0;
	    private bool isActive = true;

		//private static int BYTE_SAVE_CHUNK = 100;
		//private static int TIMESTAMP_SIZE = 4;

		/// <summary>
		/// 
		/// </summary>
		public static String DEFAULT_BYTE_FILE = "\\My Documents\\MITesAccelBytes";
		
		/// <summary>
		/// 
		/// </summary>
		public static String DEFAULT_LOG_FILE = "\\My Documents\\MITesLogFile";

		private MITesDecoder aMITesDecoder; 

		/// <summary>
		/// A full timestamp is saved after this many samples if one has not been saved
		/// due to a time overflow
		/// </summary>
		public static int TIMESTAMP_AFTER_SAMPLES = 200;

		/// <summary>
		/// 
		/// </summary>
		public static int CORRESPONDENCE_SAVE_TIME = 1000*60*10; // Once every 10 min

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesDecoder"></param>
		public MITesLoggerNew(MITesDecoder aMITesDecoder)
		{
			this.aMITesDecoder = aMITesDecoder;
			SetupFiles(DEFAULT_BYTE_FILE, DEFAULT_LOG_FILE);
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesDecoder"></param>
		/// <param name="aByteFileName"></param>
		/// <param name="aLogFileName"></param>
		public MITesLoggerNew(MITesDecoder aMITesDecoder, String aByteFileName, String aLogFileName)
		{
			this.aMITesDecoder = aMITesDecoder;
			SetupFiles(aByteFileName, aLogFileName);
		}

        /// <summary>
        /// Complete turn on/off the logger.
        /// </summary>
        /// <param name="isActive">True if logging, false otherwise</param>
        public void SetActive(bool isActive)
        {
            this.isActive = isActive;
        }

		/// <summary>
		/// Save the file in case of power loss. Allow for appending afterwards. 
		/// </summary>
		public void FlushBytes()
		{
			// Only run if file setup previously
			if (isSetup && isActive)
			{
				bw.Flush();
				bw.CloseFile();
				bw = new ByteWriter(fnData,false);
				bw.OpenFile (false);
				bwPLFormat.Flush();
				bwPLFormat.CloseFile();
				bwPLFormat = new ByteWriter(fnDataPLFormat,false);
				bwPLFormat.OpenFile (false);
			}
		}

		private bool isSetup = false;
		private void SetupFiles(String byteFileName, String logFileName)
		{
			isSetup = true;
			DateTime dt = DateTime.Now;
			int tc = Environment.TickCount; 
			fnData = byteFileName  + "." + dt.Year + "-" + dt.Month + "-" + dt.Day + "-" + dt.Hour + "-" + dt.Minute + "-" + dt.Second + "-" + dt.Millisecond + ".b";
			fnDataPLFormat = byteFileName  + "." + dt.Year + "-" + dt.Month + "-" + dt.Day + "-" + dt.Hour + "-" + dt.Minute + "-" + dt.Second + "-" + dt.Millisecond + ".PLFormat";
			logData = logFileName  + "." + dt.Year + "-" + dt.Month + "-" + dt.Day + "-" + dt.Hour + "-" + dt.Minute + "-" + dt.Second + "-" + dt.Millisecond + ".log";
			
			fw = new FileWriter(logData,false);

			WriteLogComment("TickCount at file creation: " + tc);

			bw = new ByteWriter(fnData,true);
			bw.OpenFile();
			bwPLFormat = new ByteWriter(fnDataPLFormat,true);
			bwPLFormat.OpenFile();
		}	

		int bytesFound;
		int someMITesDataIndex;

		/// <summary>
		/// 
		/// </summary>
		/// <param name="mrc"></param>
		/// <param name="aFileName"></param>
		public void GetSensorData(MITesReceiverController mrc, String aFileName)
		{
//			if (mrc.IsNewData())
//			{
				bytesFound = mrc.FillBytesBuffer(mrc.serialBytesBuffer);
			if (bytesFound > 0)
			{
			//Debug("Bytes from fill: " + bytesFound);
				someMITesDataIndex = 0; 
				someMITesDataIndex = aMITesDecoder.DecodeMITesData(mrc.serialBytesBuffer, bytesFound, aMITesDecoder.someMITesData, someMITesDataIndex);
				// Add save here
			}
			//Thread.Sleep(0);
		}


		private void moveFilesSD()
		{
			//			DirectoryInfo d = new DirectoryInfo("\\My Documents\\data");
			//			FileInfo[] fis = d.GetFiles();
			//			foreach (FileInfo fi in fis) 
			//			{      
			//				Console.WriteLine(fi);
			//				fi.MoveTo("\\Storage Card\\Data\\"  + fi.Name);
			//			}	
		}

		private void WriteBatteryLogComment(String str)
		{
			WriteLogComment("BATTERY", str);
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="commentType"></param>
		/// <param name="str"></param>
		public void WriteLogComment(String commentType, String str)
		{
            if (isActive)
            {
                fw.OpenFile(false);
                fw.WriteLine(Environment.TickCount + "," + DateTime.Now + "," + DateTime.Now.Millisecond + "," + commentType + "," + str);
                fw.CloseFile();                
            }
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="str"></param>
		public void WriteLogComment(String str)
		{
			WriteLogComment("COMMENT", str);
		}

		private void ShutdownFiles()
		{
			WriteLogComment("Shutdown file " + fnData);
			WriteLogComment("Shutdown file " + fnDataPLFormat);
			fw.Flush();
			bw.Flush();
			bwPLFormat.Flush();
			fw.CloseFile();
			bw.CloseFile();
			bwPLFormat.CloseFile();
		}

//		// Call this from setPlotVals; saveByteData(id,x,y,z);
//		private void SaveByteData(int id, int x, int y, int z)
//		{
//
//			// Write a time every 100 data points
//			if ((timeCount % 100) == 0)
//			{
//				bw.writeInt(Environment.TickCount);
//				timeCount = 0;
//			}
//			timeCount++;
// 
//			bw.writeChar((char) id);
//			bw.writeSInt(x);
//			bw.writeSInt(y);
//			bw.writeSInt(z);
//		}

//		private void WriteTimeStamp(ByteWriter byteWriter)
//		{
//			int time = Environment.TickCount;
//			byteWriter.writeInt(time);
//		}
		private void WriteTimeStampRealTime(int time)
		{
			DateTime dt = DateTime.Now;
			WriteLogComment("TICKCOUNT", time + " " + dt.Year + " " + dt.Month + " " + dt.Day + " " + dt.Hour + " " + dt.Minute + " " + dt.Second + " " + dt.Millisecond);
		}

		private void WriteFrameRate(int time)
		{
			DateTime dt = DateTime.Now;
			WriteLogComment("FRAMERATE", "" + time);
		}

		private void WriteTimeStamp(int time, ByteWriter byteWriter)
		{
            if (isActive)
	    		byteWriter.WriteInt(time);
		}

		private byte[] retBytes = new byte[6];
		private void WriteTimeStampPLFormat(double unixTime, ByteWriter byteWriter)
		{
            if (isActive)
            {
                UnixTime.GetUnixTimeBytes(unixTime, retBytes);
                byteWriter.WriteBytes(retBytes, 6);                
            }
		}

//		private byte[] saveByteBuffer = new byte[BYTE_SAVE_CHUNK];
//		private int byteSaveCount = 0;
//
//		private void SaveLastPacket(ByteWriter byteWriter)
//		{
//			SaveLastPacket(byteWriter, false); // Don't force to save, store in buffer OK
//		}


		private void SaveMITesData(MITesData aMITesData)
		{
            if (isActive)
            {
                for (int i = 0; i < MITesData.MIN_NUM_RAW_BYTES; i++)
                {
                    bw.WriteByte(aMITesData.rawBytes[i]);
                    bwPLFormat.WriteByte(aMITesData.rawBytes[i]);
                }
            }
		}

		private int diffMS = 0;
		private byte diffMSByte = 0;

        private void WriteTimeDiff(double aUnixTime, double lastUnixTime, bool isForceTimeCodeSave)
        {
            if (isActive)
            {
                diffMS = (int) (aUnixTime - lastUnixTime);

                // Save a full timestamp if forced
                // or time is > than 255 ms
                if (isForceTimeCodeSave || (diffMS > 254))
                {
                    if (diffMS >= 254)
                        Console.WriteLine("Warning; Max on MS diff: " + diffMS);
                    diffMSByte = (byte)255;
                    bw.WriteByte(diffMSByte);
                    bwPLFormat.WriteByte(diffMSByte);
                    WriteTimeStamp(aTime, bw);
                    WriteTimeStampPLFormat(aUnixTime, bwPLFormat);
                }
                else // diff MS in range and no forced timestamp save
                {
                    //				if (diffMS == 0)
                    //					Console.WriteLine ("Warning: Diff 0");
                    diffMSByte = (byte)diffMS;
                    bw.WriteByte(diffMSByte);
                    bwPLFormat.WriteByte(diffMSByte);
                }
            }
        }

        //private void WriteTimeDiff(int aTime, int lastTime, double unixTime, bool isForceTimeCodeSave)
        //{
        //    if (isActive)
        //    {
        //        diffMS = aTime - lastTime;

        //        // Save a full timestamp if forced
        //        // or time is > than 255 ms
        //        if (isForceTimeCodeSave || (diffMS > 254))
        //        {
        //            if (diffMS >= 254)
        //                Console.WriteLine("Warning; Max on MS diff: " + diffMS);
        //            diffMSByte = (byte) 255;
        //            bw.WriteByte(diffMSByte);
        //            bwPLFormat.WriteByte(diffMSByte);
        //            WriteTimeStamp(aTime, bw);
        //            WriteTimeStampPLFormat(unixTime, bwPLFormat);
        //        }
        //        else // diff MS in range and no forced timestamp save
        //        {
        //            //				if (diffMS == 0)
        //            //					Console.WriteLine ("Warning: Diff 0");
        //            diffMSByte = (byte) diffMS;
        //            bw.WriteByte(diffMSByte);
        //            bwPLFormat.WriteByte(diffMSByte);
        //        }
        //    }
        //}

	    private int timeSaveCount = TIMESTAMP_AFTER_SAMPLES; 
		private int correspondSaveTime = 0; 
		private int aTime = 0;
		private double aUnixTime = 0; 
		private int lastTime = 0;
        private double lastUnixTime = 0; 

		/// <summary>
		/// For each 5 byte packet, first save the ms-offset marker byte. Then save either the
		/// timecode then the data or the data itself. 
		/// </summary>
        public void SaveRawData()
		{
		    if (isActive)
		    {
		        for (int i = 0; i < aMITesDecoder.someMITesDataIndex; i++)
		        {
		            aTime = aMITesDecoder.someMITesData[i].timeStamp;
		            aUnixTime = aMITesDecoder.someMITesData[i].unixTimeStamp;

		            //Console.WriteLine ("Time: " + aTime);

		            // Roughly once per second save full timestamp, no matter what
		            if (timeSaveCount == TIMESTAMP_AFTER_SAMPLES)
		            {
		                //WriteTimeDiff(aTime, lastTime, aUnixTime, true); // Force save
                        WriteTimeDiff(aUnixTime, lastUnixTime, true); // Force save
                        timeSaveCount = 0;
		            }
		            else
		            {
		                //WriteTimeDiff(aTime, lastTime, aUnixTime, false);
                        WriteTimeDiff(aUnixTime, lastUnixTime, false); // Force save
                        timeSaveCount++;
		            }

		            // Actually save the data! 
		            SaveMITesData(aMITesDecoder.someMITesData[i]);

		            lastTime = aTime;
		            lastUnixTime = aUnixTime; 
		        }
		    }
		}

//			LastPacket(ByteWriter byteWriter, bool isForceWrite)
//		{
//			// Currently assumes byteWriter file is opened and ready to go. Fix that. 
//			
//			if (byteSaveCount >= (BYTE_SAVE_CHUNK-PACKET_SIZE-TIMESTAMP_SIZE))
//			{
//				// byteSaveBuffer full, so write it
//				byteWriter.writeBytes(saveByteBuffer, byteSaveCount);
//				WriteTimeStamp(byteWriter);
//				byteSaveCount = 0;
//			}
//
//			// Add to saveByteBuffer
//			for (int i = 0; i < PACKET_SIZE; i++)
//				saveByteBuffer[byteSaveCount++] = packet[i];
//
//			if (isForceWrite)
//			{
//				// Save forced for the last packet
//				byteWriter.writeBytes(saveByteBuffer, byteSaveCount);
//				byteSaveCount = 0;
//			}
//		}
	}
}
