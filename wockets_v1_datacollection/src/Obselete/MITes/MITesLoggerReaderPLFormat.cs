using System;
using System.Collections;
using System.IO;
using System.Threading;
using HousenCS.IO;
using HousenCS.MITes;

namespace HousenCS.MITes
{
	/// <summary>
	/// A MITesLoggerReader that reads data saved in the PLFormat. 
	/// </summary>
	public class MITesLoggerReaderPLFormat
	{
        private class BFileInfo
        {
            public BFileInfo()
            {
            }

            //public DateTime startTime;
            public string fileRec1 = "";
        }

	    private static DateTime aRefDate = DateTime.Now;
	    private static bool isRefDateSet = false; 

        private ByteReader br;
        private int fileIndex = 0; 
        private MITesDecoder aMITesDecoder;
        ArrayList someBinaryFiles = new ArrayList();

        private void GenerateBinaryFileList(string aDataDir)
        {
            string[] someDays1 = new string[0];

            // First, find all days 
            someDays1 = Directory.GetDirectories(aDataDir); 
            
            //Merge and sort the days from both receiver directories 
            ArrayList someDays = new ArrayList();

            foreach (string d in someDays1)
            {
                someDays.Add(Path.GetFileName(d));
            }
            someDays.Sort();

            foreach (string d in someDays)
            {
                Console.WriteLine("DAY: " + d);
            } 

            // Now that we have a list of days sorted by date, go into each folder
            // and put together ordered list of binary files. 

            foreach (string d in someDays)
            {
                // Loop over possible hours and add to list
                for (int i = 0; i < 24; i++)
                {
                    BFileInfo aBFileInfo = new BFileInfo();
                    // Check for hour dir in rec 1
                    if (Directory.Exists(aDataDir + "\\" + d + "\\" + i))
                        aBFileInfo.fileRec1 = GetBinaryMITesFile(aDataDir + "\\" + d + "\\" + i);

                    // Add if one of the receiver directories had a file
                    if (aBFileInfo.fileRec1 != "")
                        someBinaryFiles.Add(aBFileInfo);
                }
            }
            Console.WriteLine(someBinaryFiles); 
        }

        /// <summary>
        /// Look for a MITesAccelBytes*.b file and return the full path
        /// </summary>
        /// <param name="aDirPath"></param>
        /// <returns></returns>
        private string GetBinaryMITesFile(string aDirPath)
        {
            string[] matchFiles = Directory.GetFiles(aDirPath, "MITesAccelBytes*.b");
            if (matchFiles.Length != 1)
            {
                Console.WriteLine("No data file found in " + aDirPath);
                return ""; 
            }
            else
            {
                return matchFiles[0];
            }            
        }

		/// <summary>
		/// Initialize an object that will read raw binary data in PlaceLab multi-receiver format and open first files.
		/// </summary>
		/// <param name="aMITesDecoder">MITesDecoder object</param>
        /// <param name="aDataDir">Data directory for MITes data</param>
        public MITesLoggerReaderPLFormat(MITesDecoder aMITesDecoder, String aDataDir)
		{
		    GenerateBinaryFileList(aDataDir);

			this.aMITesDecoder = aMITesDecoder;
            SetupNextFiles(0);
		}

        /// <summary>
        /// Check if the dirPath is in the expected format. 
        /// </summary>
        /// <param name="aDirPath"></param>
        public static bool IsValidDirectory(string aDirPath)
        {
            string sensorDataFile = aDirPath + "\\SensorData.xml";
            string activityLabelsFile = aDirPath + "\\ActivityLabelsRealtime.xml";

            if (File.Exists(sensorDataFile) &&
                File.Exists(activityLabelsFile))
                return true;
            else
                return false; 
        }

	    private bool SetupNextFiles(int index)
		{
	        dTimeStamp1 = 0;
	        dTimeStamp2 = 0; 

            if (br != null)
                br.CloseFile();

	        br = null;
	       
	        string f1 = ((BFileInfo) someBinaryFiles[index]).fileRec1;  
            if (f1 != "")
            {
                br = new ByteReader(f1);
                br.OpenFile();              
                Console.WriteLine("Opening file for read: " + f1);
            }

            if (br == null)
                return false;
            else
                return true;                 
		}

		private static byte[] b = new byte[1];
        private static int[] ts = new int[1];
		
        ///// <summary>
        ///// 
        ///// </summary>
        ///// <param name="br"></param>
        ///// <param name="theLastTime"></param>
        ///// <returns></returns>
        ////public static int ReadTimeStamp(ByteReader br, int theLastTime)
        //{
        //    int lastTime = theLastTime;  
        //    //Console.WriteLine ("Read time stamp");
        //    bool readValid = br.ReadByte(b);

        //    if (!readValid)
        //    {
        //        return MITesData.NONE;
        //    }

        //    if (b[0] == ((int) 255))
        //    {
        //        //Console.WriteLine ("Marker");
        //        // Marker, so read the whole timecode
        //            br.ReadInt (ts);
        //            lastTime = ts[0];
        //            //Console.WriteLine ("Timecode: " + lastTime);
        //    }
        //    else
        //    {
        //        // Read only the difference between this and previous time (less than 255 ms)
        //        lastTime += (int) b[0];
        //        //Console.WriteLine ("Diff byte: " + b[0] + " modified Timecode: " + lastTime);
        //    }
        //    return lastTime;
        //}

        private static byte[] b6 = new byte[6];

        private static byte[] refByte = { 0x7e, 0x7e, 0x7e, 0x7e, 0x7e, 0x7e };
        private static double refTime = UnixTime.DecodeUnixTimeCodeBytes(refByte);

        private static int junkTimecodeData = 0; 

    /// <summary>
    /// 
    /// </summary>
    /// <param name="br"></param>
    /// <param name="aLastUnixTime"></param>
    /// <returns></returns>
        public static double ReadUnixTimeStamp(ByteReader br, double aLastUnixTime)
		{
		    double lastUnixTime = aLastUnixTime; 
			//Console.WriteLine ("Read UNIX time stamp");

            if (br == null)
                return 0;

			bool readValid = br.ReadByte(b);

			if (!readValid)
			{
				return MITesData.NONE;
			}

			if (b[0] == ((int) 255))
			{
                //Console.WriteLine("Marker: " + debugCount);
				// Marker, so read the whole timecode
				readValid = br.ReadBytes(b6);

                if (!readValid)
                    return MITesData.NONE; 

				lastUnixTime = UnixTime.DecodeUnixTimeCodeBytesFixed(b6); // SSI Added test

                DateTime junk = new DateTime();

                if (lastUnixTime == refTime)
                {
                    // This is a the so-called sync byte. Need to read 5 more bytes and ignore
                    for (int r = 0; r < 5; r++)
                    {
                        readValid = br.ReadByte(b);

                        if (!readValid)
                            return MITesData.NONE; 
                    }
                    Console.WriteLine("SYNC byte: keep time as: " + lastUnixTime);

                    //Now read the time byte and add to the existing time
                    readValid = br.ReadByte(b);
                    
                    if (!readValid)
                        return MITesData.NONE;
                    
                    return aLastUnixTime + (int)b[0];
                }
                else
                {
                    //Console.WriteLine ("UNIX Timecode: " + lastUnixTime);
                    UnixTime.GetDateTime((long)lastUnixTime, out junk);
                    Console.WriteLine("UNIX Timecode date: " + junk + " " + lastUnixTime);                    
                }

                //junk = new DateTime(2007,9,9,8,16,5,609);
                //double junkme = UnixTime.GetUnixTime(junk);
                //UnixTime.GetDateTime((long)junkme,out junk);
                //Console.WriteLine("NEW DATE: " + junk);
                //byte[] somebytes = UnixTime.GetUnixTimeBytes(junkme);
                //double newUnixTime = UnixTime.DecodeUnixTimeCodeBytesFixed(somebytes);
                //UnixTime.GetDateTime((long) newUnixTime, out junk); 
                //Console.WriteLine("NEW DATE: " + junk);

                if (!isRefDateSet)
                {
                    aRefDate = junk.AddDays(-2);
                    isRefDateSet = true;                     
                }

                //lastUnixTime = UnixTime.DecodeUnixTimeCodeBytesFixed(b6);
                //DateTime dt = new DateTime();
                //UnixTime.GetDateTime((long) lastUnixTime, out dt);
                //Console.WriteLine("TEST: " + dt);                
			}
			else
			{

                if (lastUnixTime == 0)
                {
                    junkTimecodeData++;

                    if ((junkTimecodeData % 5000) == 0)
                    {
                        Console.WriteLine("ERROR: Hit " + junkTimecodeData + " of junk timecode data."); //"Last unix time is zero for some reason!");                        
                        junkTimecodeData = 0;
                    }
                }
                else
                {
                    // Read only the difference between this and previous time (less than 255 ms)
                    lastUnixTime += (int)b[0];
                    //Console.WriteLine ("Diff byte: " + b[0] + " modified UNIX Timecode: " + lastUnixTime);                    
                }
            }
			return lastUnixTime;
		}

		static byte[] temp = new byte[1];
		int someMITesDataIndex;


        private double dTimeStamp1 = 0;
        private double dTimeStamp2 = 0;
        private double dLastTimeStamp1 = 0;
        private double dLastTimeStamp2 = 0;
        private double lastTimeStampTime1 = 0;
        private double lastTimeStampTime2 = 0; 

        private bool isEndFile1 = false;
	    private bool isEndFile2 = false;
        //private int timeToWait1 = 0;
        //private int timeToWait2 = 0;

        private byte[] tempByte = new byte[1];

        private DateTime GetDateTime(double aUnixTime)
        {
            DateTime dt = new DateTime();
            UnixTime.GetDateTime((long) aUnixTime,out dt);
            return dt; 
        }

        private double lastGoodTime1 = 0;
        private double lastGoodTime2 = 0;
//	    private bool isLastMatch = true;
	    private static long debugCount = 0;

        private void IgnorePacket(ByteReader brTemp)
        {
            if (brTemp != null)
            {
                brTemp.ReadByte(tempByte);
                brTemp.ReadByte(tempByte);
                brTemp.ReadByte(tempByte);
                brTemp.ReadByte(tempByte);
                brTemp.ReadByte(tempByte);
            }
        }

        /// <summary>
        /// Decode multiple receiver data that has been saved by MITesLogger (always send multiple of 4 bytes). A MITesLogger saves
        /// MITesData. This reads it back in so it behaves exactly as data read from the 
        /// serial port. Useful for "playing back" data that has been saved. 
        /// </summary>
        /// <param name="someData">The array in which the resulting MITesData will be stored.</param>
        /// <param name="dataIndex">The current index of the array in which the MITesData will be stored. (This will append data onto the end of existing data if needed).</param>
        /// <param name="br1">A ByteReader object that has been opened to the proper file for receiver 1.</param>
        /// <returns>The new index for the someData array.</returns>
        public int DecodePLFormatMR(MITesData[] someData, int dataIndex, ByteReader br1)
        {
            bool isGoodPacketRead = false;
            isEndFile1 = false;

            int fileUsed = 0; 

            // Determine if consumed next data point from each file. Value of 0 indicates yes and get next value. 

            if (dTimeStamp1 == 0)
                dTimeStamp1 = ReadUnixTimeStamp(br1, dLastTimeStamp1);

            if ((dTimeStamp1 - dLastTimeStamp1) > (2 * 60 * 60 * 1000))
                Console.WriteLine("Skip of more than two hours in file 1");

            debugCount++;

            DateTime dt1 = new DateTime();
            UnixTime.GetDateTime((long)dTimeStamp1, out dt1);

            //if (((dTimeStamp1 != MITesData.NONE) && (dTimeStamp2 != MITesData.NONE)) &&
            //    ((dt1.Second != dt2.Second) || (dt1.Minute != dt2.Minute)))
            //{
            //    //isLastMatch = false;
            //        Console.WriteLine("DATES: " + Environment.NewLine + dt1 + Environment.NewLine + dt2 + "    " + debugCount);
            //}

            if ((dTimeStamp1 == (double)MITesData.NONE) || (br1 == null))
            {
                //Console.WriteLine("End of file 1: " + GetDateTime(lastGoodTime1) + " " + GetDateTime(lastGoodTime2));
                isEndFile1 = true;
            }

            if (isEndFile1)
            {
                Console.WriteLine("End of file.");
                return 0;                
            }

            // If at this point, there is some data to read in one of the files 

            #region Thread wait (do in the future) 
            // Insert waiting code here in the future for graphing capability option 
            //diffMS1 = (int)(dTimeStamp1 - dLastTimeStamp1);
            //if ((dLastTimeStamp1 != 0) && (dTimeStamp1 != 0))
            //    timeToWait1 = diffMS1;
            //else
            //    timeToWait1 = 0;

            //diffMS2 = (int)(dTimeStamp1 - dLastTimeStamp1);
            //if ((dLastTimeStamp1 != 0) && (dTimeStamp1 != 0))
            //    timeToWait2 = diffMS1;
            //else
            //    timeToWait2 = 0;

            //// Wait the right number of MS if needed from last time data grabbed
            //diffTime = Environment.TickCount - lastTimeStampTime;
            //if ((timeToWait - diffTime) > 0)
            //{
            //    Thread.Sleep(timeToWait - diffTime);
            //    timeToWait = 0;
            //}

            #endregion

            if ((dTimeStamp1 != -1) && (dLastTimeStamp1 != -1) && (dTimeStamp1 < dLastTimeStamp1))
                Console.WriteLine("Jumpback: " + debugCount + " " + (dLastTimeStamp1 - dTimeStamp1)); 

            dLastTimeStamp1 = dTimeStamp1;
            lastTimeStampTime1 = Environment.TickCount;

            // Read packet that is first in time from whichever file. Leave other be  

            ByteReader brTemp;

            brTemp = null; 

            if (!isEndFile1)
            {
                lastGoodTime1 = dTimeStamp1;
                brTemp = br1;
                fileUsed = 1;
            }

            // Check if need to ignore data because we have a bad timestamp 
            // in either of the files. If so, read bytes and ignore.
            if (fileUsed == 0)
            {
                if (dTimeStamp1 == 0)
                    IgnorePacket(br1);
            }

            if (fileUsed != 0)
            {
                isGoodPacketRead = brTemp.ReadByte(tempByte);
                aMITesDecoder.packet[0] = tempByte[0];
                brTemp.ReadByte(tempByte);
                aMITesDecoder.packet[1] = tempByte[0];
                brTemp.ReadByte(tempByte);
                aMITesDecoder.packet[2] = tempByte[0];
                brTemp.ReadByte(tempByte);
                aMITesDecoder.packet[3] = tempByte[0];
                brTemp.ReadByte(tempByte);
                aMITesDecoder.packet[4] = tempByte[0];
                aMITesDecoder.DecodeLastPacket(someData[dataIndex], false); // Don't swap bytes             
                if (!isGoodPacketRead)
                    someData[dataIndex].type = (int)MITesTypes.NOISE;
            }

            //Console.WriteLine("FileUsed: " + fileUsed);

            if (fileUsed == 1)
            {
                someData[dataIndex].timeStamp = UnixTime.IntTimeFromUnixTime(dTimeStamp1,aRefDate);
                aMITesDecoder.SetUnixTime(someData[dataIndex], dTimeStamp1); // Set the time
                someData[dataIndex].fileID = 1;

                // If not a good timestamp (probably because haven't gotten marker yet) set to noise
                if (dTimeStamp1 == 0)
                {
                    someData[dataIndex].type = (int)MITesTypes.NOISE;
                    //Console.WriteLine("Losing data due to lack of timestamp sync.");
                }

                dTimeStamp1 = 0; // Reset so gets read next time from file 
            }
            else
            {
                //Console.WriteLine("ERROR: no file used");
                return -1;
            }

//            dataIndex++;
            return 1;
        }

        private bool isNewFiles = true; 
		/// <summary>
		/// Grab sensor data from the saved MITesLogger binary file and use a MITesDecoder to decode it. 
		/// </summary>
		/// <param name="numPackets">The number of MITes packets to get</param>
        public bool GetSensorData(int numPackets)
		{
		    someMITesDataIndex = 0;
		    int tmpIndex = DecodePLFormatMR(aMITesDecoder.someMITesData, someMITesDataIndex, br);
            if (tmpIndex == -1) // Data, but not valid timecodes 
            {
                aMITesDecoder.someMITesDataIndex = 0;
                return true;
            }
            else if (tmpIndex == 0)
		    {
                // Both files reached endpoints so go to next set of files for new hour
		        fileIndex += 1;
                if (fileIndex < someBinaryFiles.Count)
                {
                    isNewFiles = SetupNextFiles(fileIndex);
                    if (!isNewFiles)
                        return false;

                    dLastTimeStamp1 = lastGoodTime1;

                    tmpIndex = DecodePLFormatMR(aMITesDecoder.someMITesData, someMITesDataIndex, br);
 
                    if (tmpIndex == 0)
                    {
                        Console.WriteLine("ERROR: Should not have gotten this twice!!!  ---------------");
                        return false; 
                    }
                    else
                    {
                        aMITesDecoder.someMITesDataIndex = tmpIndex;
                        return true;
                    }
                }
                else
                {
                    aMITesDecoder.someMITesDataIndex = 0; // End of all data
                    return false;                     
                }
		    }
		    else
		    {
		        aMITesDecoder.someMITesDataIndex = tmpIndex;
		        return true; 
		    }
        }

	    private void ShutdownFiles()
		{
            if (br != null)
	    		br.CloseFile();
        }
	}
}