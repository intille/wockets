using System;
using System.Collections;
using System.IO;
using System.Threading;
using HousenCS.IO;
using HousenCS.MITes;


namespace HousenCS.MITes
{
    public class MITesLoggerReader
    {
               


	    private static DateTime aRefDate = DateTime.Now;
	    private static bool isRefDateSet = false; 

        private ByteReader br;


        private int fileIndex = 0; 

        private MITesDecoder aMITesDecoder;

        ArrayList someBinaryFiles = new ArrayList();

        private void GenerateBinaryFileList(string aDataDir)
        {
            string rawDirectory=aDataDir + "\\data\\raw\\PLFormat";

            if (Directory.Exists(rawDirectory)==false)
                return;

            string[] subdirectories = Directory.GetDirectories(rawDirectory);
            foreach (string subdirectory in subdirectories)
            {
                for (int i = 0; i < 30; i++)
                {
                    if (Directory.Exists(subdirectory + "\\" + i))
                    {
                        string[] matchingFiles = GetBinaryMITesFile(subdirectory + "\\" + i);
                        for (int j=0;(j<matchingFiles.Length);j++)
                            someBinaryFiles.Add(matchingFiles[j]);
                    }
                }
            }
            
            Console.WriteLine(someBinaryFiles); 
        }

        /// <summary>
        /// Look for a MITesAccelBytes*.b file and return the full path
        /// </summary>
        /// <param name="aDirPath"></param>
        /// <returns></returns>
        private string[] GetBinaryMITesFile(string aDirPath)
        {
            string[] matchFiles = Directory.GetFiles(aDirPath, "MITesAccelBytes*.PLFORMAT");
            if (matchFiles.Length==0)
                matchFiles = Directory.GetFiles(aDirPath, "MITesAccelBytes*.0.b");
            return matchFiles;
            /*
            if (matchFiles.Length != 1)
            {
                Console.WriteLine("No data file found in " + aDirPath);
                return ""; 
            }
            else
            {
                return matchFiles[0];
            }*/            
        }

		/// <summary>
		/// Initialize an object that will read raw binary data in PlaceLab multi-receiver format and open first files.
		/// </summary>
		/// <param name="aMITesDecoder">MITesDecoder object</param>
        /// <param name="aDataDir">Data directory for MITes data</param>
        public MITesLoggerReader(MITesDecoder aMITesDecoder, String aDataDir)
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
            string subjectDataFile = aDirPath + "\\SubjectData.xml";
            string sensorDataFile = aDirPath + "\\SensorData.xml";
            string activityLabelsFile = aDirPath + "\\ActivityLabels.xml";

            if (File.Exists(subjectDataFile) &&
                File.Exists(sensorDataFile) &&
                File.Exists(activityLabelsFile))
                return true;
            else
                return false; 
        }

	    private bool SetupNextFiles(int index)
		{
	        dTimeStamp = 0;


            if (br != null)
                br.CloseFile();


	        br = null;

	        string f = ((string) someBinaryFiles[index]);  
	          
            if (f != "")
            {
                br = new ByteReader(f);
                br.OpenFile();              
                Console.WriteLine("Opening file for read: " + f);
            }

            if (br == null)
                return false;
            else            
                return true;                             
		}

        //static int MAX_BYTES = 5 * 30;
        //byte[] someBytes = new byte[MAX_BYTES];  

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
			bool readValid = br.ReadByte(b);

			if (!readValid)
			{
				return MITesData.NONE;
			}

			if (b[0] == ((int) 255))
			{
                Console.WriteLine("Marker: " + debugCount);
				// Marker, so read the whole timecode
				readValid = br.ReadBytes(b6);

                if (!readValid)
                    return MITesData.NONE; 

				lastUnixTime = UnixTime.DecodeUnixTimeCodeBytesFixed(b6); // SSI Added test

                if (lastUnixTime == refTime)
                {
                    // This is a the so-called sync byte. Need to read 5 more bytes and ignore
                    for (int r = 0; r < 5; r++)
                    {
                        readValid = br.ReadByte(b);

                        if (!readValid)
                            return MITesData.NONE; 
                    }
                    //Console.WriteLine("SYNC byte: keep time as: " + lastUnixTime);

                    //Now read the time byte and add to the existing time
                    readValid = br.ReadByte(b);
                    
                    if (!readValid)
                        return MITesData.NONE;
                    
                    return aLastUnixTime + (int)b[0];
                }

			    //Console.WriteLine ("UNIX Timecode: " + lastUnixTime);
                DateTime junk = new DateTime();
                UnixTime.GetDateTime((long)lastUnixTime, out junk);
                //Console.WriteLine("UNIX Timecode date: " + junk);

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
                    Console.WriteLine("ERROR: Last unix time is zero for some reason!");
                }
				// Read only the difference between this and previous time (less than 255 ms)
				lastUnixTime += (int) b[0];
				//Console.WriteLine ("Diff byte: " + b[0] + " modified UNIX Timecode: " + lastUnixTime);
			}
			return lastUnixTime;
		}

		static byte[] temp = new byte[1];
		int someMITesDataIndex;


        private double dTimeStamp = 0;

        private double dLastTimeStamp = 0;
        //private int diffTime1 = 0;  
        //private int diffTime2 = 0;
        //private int diffMS1 = 0;
        //private int diffMS2 = 0;
        private double lastTimeStampTime = 0;


        private bool isEndFile = false;

        //private int timeToWait1 = 0;
        //private int timeToWait2 = 0;

        private byte[] tempByte = new byte[1];

        private DateTime GetDateTime(double aUnixTime)
        {
            DateTime dt = new DateTime();
            UnixTime.GetDateTime((long) aUnixTime,out dt);
            return dt; 
        }

        private double lastGoodTime = 0;

//	    private bool isLastMatch = true;
	    private static long debugCount = 0;

        /// <summary>
        /// Decode multiple receiver data that has been saved by MITesLogger (always send multiple of 4 bytes). A MITesLogger saves
        /// MITesData. This reads it back in so it behaves exactly as data read from the 
        /// serial port. Useful for "playing back" data that has been saved. 
        /// </summary>
        /// <param name="someData">The array in which the resulting MITesData will be stored.</param>
        /// <param name="dataIndex">The current index of the array in which the MITesData will be stored. (This will append data onto the end of existing data if needed).</param>
        /// <param name="br1">A ByteReader object that has been opened to the proper file for receiver 1.</param>
        /// <param name="br2">A ByteReader object that has been opened to the proper file for receiver 2.</param>
        /// <returns>The new index for the someData array.</returns>
        public int DecodePLFormat(MITesData[] someData, int dataIndex, ByteReader br)
        {
            isEndFile = false;

            // Determine if consumed next data point from each file. Value of 0 indicates yes and get next value. 

            if (dTimeStamp == 0)
                dTimeStamp = ReadUnixTimeStamp(br, dLastTimeStamp);


            debugCount++;

            DateTime dt = new DateTime();
            UnixTime.GetDateTime((long)dTimeStamp, out dt);


            //if (((dTimeStamp1 != MITesData.NONE) && (dTimeStamp2 != MITesData.NONE)) &&
            //    ((dt1.Second != dt2.Second) || (dt1.Minute != dt2.Minute)))
            //{
            //    //isLastMatch = false;
            //        Console.WriteLine("DATES: " + Environment.NewLine + dt1 + Environment.NewLine + dt2 + "    " + debugCount);
            //}

            if (dTimeStamp == (double)MITesData.NONE)
            {
                //Console.WriteLine("End of file 1: " + GetDateTime(lastGoodTime1) + " " + GetDateTime(lastGoodTime2));
                isEndFile = true; 
            }



            if (isEndFile)
            {
                Console.WriteLine("End of both files.");
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

            if ((dTimeStamp != -1) && (dLastTimeStamp != -1) && (dTimeStamp < dLastTimeStamp))
                Console.WriteLine("Jumpback1: " + debugCount);
    

            dLastTimeStamp = dTimeStamp;
            lastTimeStampTime = Environment.TickCount;

            //DateTime junkme = new DateTime();
            //UnixTime.GetDateTime((long) dTimeStamp1, out junkme);
            //Console.WriteLine("                               DTIMESTAMP1: " + junkme);

            //UnixTime.GetDateTime((long)dTimeStamp2, out junkme);
            //Console.WriteLine("                               DTIMESTAMP2: " + junkme);


            // Read packet that is first in time from whichever file. Leave other be  


                if ((dTimeStamp != 0) && (!isEndFile))
                {
                    lastGoodTime = dTimeStamp;
                }

                else
                {
                    Console.WriteLine("ERROR2 -- Should not be here!! ----------------------------");
                }

            br.ReadByte(tempByte);
            aMITesDecoder.packet[0] = tempByte[0];
            br.ReadByte(tempByte);
            aMITesDecoder.packet[1] = tempByte[0];
            br.ReadByte(tempByte);
            aMITesDecoder.packet[2] = tempByte[0];
            br.ReadByte(tempByte);
            aMITesDecoder.packet[3] = tempByte[0];
            br.ReadByte(tempByte);
            aMITesDecoder.packet[4] = tempByte[0];

            if (aMITesDecoder.packet[0] == MITesDecoder.MAX_CHANNEL)
            {
                br.ReadByte(tempByte);
                aMITesDecoder.packet[5] = tempByte[0];
            }
            else
                aMITesDecoder.packet[5] = 0;

            //if the packet is for an HTC phone (i.e. packet[1]>=50)... read 1 additional byte

            aMITesDecoder.DecodeLastPacket(someData[dataIndex], false); // Don't swap bytes

            //Console.WriteLine("FileUsed: " + fileUsed);

                
            someData[dataIndex].timeStamp = UnixTime.IntTimeFromUnixTime(dTimeStamp,aRefDate);
                
            aMITesDecoder.SetUnixTime(someData[dataIndex], dTimeStamp); // Set the time            
            someData[dataIndex].fileID = 1;                 
            dTimeStamp = 0; // Reset so gets read next time from file 


//            dataIndex++;
            return 1;
        }









        public int DecodeWocketsPLFormat(MITesData[] someData, int dataIndex, ByteReader br)
        {
            isEndFile = false;

            // Determine if consumed next data point from each file. Value of 0 indicates yes and get next value. 

            if (dTimeStamp == 0)
                dTimeStamp = ReadUnixTimeStamp(br, dLastTimeStamp);


            debugCount++;

            DateTime dt = new DateTime();
            UnixTime.GetDateTime((long)dTimeStamp, out dt);


            //if (((dTimeStamp1 != MITesData.NONE) && (dTimeStamp2 != MITesData.NONE)) &&
            //    ((dt1.Second != dt2.Second) || (dt1.Minute != dt2.Minute)))
            //{
            //    //isLastMatch = false;
            //        Console.WriteLine("DATES: " + Environment.NewLine + dt1 + Environment.NewLine + dt2 + "    " + debugCount);
            //}

            if (dTimeStamp == (double)MITesData.NONE)
            {
                //Console.WriteLine("End of file 1: " + GetDateTime(lastGoodTime1) + " " + GetDateTime(lastGoodTime2));
                isEndFile = true;
            }



            if (isEndFile)
            {
                Console.WriteLine("End of both files.");
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

            if ((dTimeStamp != -1) && (dLastTimeStamp != -1) && (dTimeStamp < dLastTimeStamp))
                Console.WriteLine("Jumpback1: " + debugCount);


            dLastTimeStamp = dTimeStamp;
            lastTimeStampTime = Environment.TickCount;

            //DateTime junkme = new DateTime();
            //UnixTime.GetDateTime((long) dTimeStamp1, out junkme);
            //Console.WriteLine("                               DTIMESTAMP1: " + junkme);

            //UnixTime.GetDateTime((long)dTimeStamp2, out junkme);
            //Console.WriteLine("                               DTIMESTAMP2: " + junkme);


            // Read packet that is first in time from whichever file. Leave other be  


            if ((dTimeStamp != 0) && (!isEndFile))
            {
                lastGoodTime = dTimeStamp;
            }

            else
            {
                Console.WriteLine("ERROR2 -- Should not be here!! ----------------------------");
            }

            br.ReadByte(tempByte);
            aMITesDecoder.packet2[0] = tempByte[0];
            br.ReadByte(tempByte);
            aMITesDecoder.packet2[1] = tempByte[0];
            br.ReadByte(tempByte);
            aMITesDecoder.packet2[2] = tempByte[0];
            br.ReadByte(tempByte);
            aMITesDecoder.packet2[3] = tempByte[0];
            br.ReadByte(tempByte);
            aMITesDecoder.packet2[4] = tempByte[0];
            br.ReadByte(tempByte);
            aMITesDecoder.packet2[5] = tempByte[0];
            br.ReadByte(tempByte);
            aMITesDecoder.packet2[6] = tempByte[0];


            //if the packet is for an HTC phone (i.e. packet[1]>=50)... read 1 additional byte
            aMITesDecoder.DecodeWocketsFrame(someData[dataIndex], aMITesDecoder.packet2);
            //aMITesDecoder.DecodeLastPacket(someData[dataIndex], false); // Don't swap bytes

            //Console.WriteLine("FileUsed: " + fileUsed);


            someData[dataIndex].timeStamp = UnixTime.IntTimeFromUnixTime(dTimeStamp, aRefDate);

            aMITesDecoder.SetUnixTime(someData[dataIndex], dTimeStamp); // Set the time            
            someData[dataIndex].fileID = 1;
            dTimeStamp = 0; // Reset so gets read next time from file 


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
#if (PocketPC)
                    int tmpIndex = DecodeWocketsPLFormat(aMITesDecoder.someMITesData, someMITesDataIndex, br);
#else
            //int tmpIndex = DecodeWocketsPLFormat(aMITesDecoder.someMITesData, someMITesDataIndex, br);
             int tmpIndex = DecodePLFormat(aMITesDecoder.someMITesData, someMITesDataIndex, br);
#endif
		    if (tmpIndex == 0)
		    {
		        fileIndex += 1;
                if (fileIndex < someBinaryFiles.Count)
                {
                    isNewFiles = SetupNextFiles(fileIndex);                    
                    isRefDateSet = false; 
                    if (!isNewFiles)
                        return false;

                    dLastTimeStamp = lastGoodTime;

#if (PocketPC)
                    tmpIndex = DecodeWocketsPLFormat(aMITesDecoder.someMITesData, someMITesDataIndex, br);
#else
                    //tmpIndex = DecodeWocketsPLFormat(aMITesDecoder.someMITesData, someMITesDataIndex, br);
                   tmpIndex = DecodePLFormat(aMITesDecoder.someMITesData, someMITesDataIndex, br);
#endif
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
