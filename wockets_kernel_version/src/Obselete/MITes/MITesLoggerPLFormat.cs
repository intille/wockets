using System;
using System.Diagnostics;
using System.Threading;
using HousenCS.IO;
using HousenCS.MITes;

namespace HousenCS.MITes
{
    /// <summary>
    /// A MITesLoggerPLFormat saves MITes data into the binary PlaceLab format, with 
    /// timestamped filenames and directories (by hour).  
    /// </summary>
    public class MITesLoggerPLFormat
    {
        private ByteWriter bwPLFormat = null; 
        private String currentDataFile = "";
        private bool isActive = true;
        private string aRootPathName = ""; 
        private MITesDecoder aMITesDecoder;      
        private int presentHour = -1;
        private string dayPath = "";
        public const string FILE_EXT = "b";
        public const string COMP_ID = "0";
        public const string FILE_TYPE_MONIKER = "MITesAccelBytes";

        /// <summary>
        /// A full timestamp is saved after this many samples if one has not been saved
        /// due to a time overflow. This is a good idea because of clock inaccuracies
        /// that might add up over time. 
        /// </summary>
        public static int TIMESTAMP_AFTER_SAMPLES = 200;
        //private System.IO.TextWriter tw;
        /// <summary>
        /// Sets up an object to save raw MITes data in the PlaceLab format, with binary files by the hour.
        /// </summary>
        /// <param name="aMITesDecoder">The ojbect containing the decoded data.</param>
        /// <param name="aFilePath">The directory where the data will be saved.</param>
        public MITesLoggerPLFormat(MITesDecoder aMITesDecoder, String aFilePath)
        {
            this.aMITesDecoder = aMITesDecoder;
            aRootPathName = aFilePath; 
            DetermineFilePath();
            //tw = new System.IO.StreamWriter(@"\Internal Storage\test\data-written.csv");
        }

        /// <summary>
        /// Save the file in case of power loss. Allow for appending afterwards. 
        /// </summary>
        public void FlushBytes()
        {
            // Only run if file setup previously
            if (bwPLFormat != null)
            {
                bwPLFormat.Flush();
                bwPLFormat.CloseFile();
                bwPLFormat = new ByteWriter(currentDataFile, false);
                bwPLFormat.OpenFile(false);
            }
        }

        /// <summary>
        /// Determine and create the directory where the raw data is saved in 1-hour chunks. 
        /// </summary>
        private void DetermineFilePath()
        {
            if (isActive)
            {
                if (presentHour != DateTime.Now.Hour)
                {
                    if (bwPLFormat != null)
                        bwPLFormat.CloseFile();
                    presentHour = DateTime.Now.Hour;
                    // Need to create a new directory and switch the file name
                    dayPath = DirectoryStructure.DayDirectoryToUse(aRootPathName);

                    // Make sure hour directory exists 
                    currentDataFile = dayPath + "\\" + presentHour + "\\";
                    if (!System.IO.Directory.Exists(currentDataFile))
                        System.IO.Directory.CreateDirectory(currentDataFile);

                    currentDataFile = currentDataFile + FILE_TYPE_MONIKER + "." +
                                   DirectoryStructure.GetDate() + "." + COMP_ID + "." + FILE_EXT;

                    bwPLFormat = new ByteWriter(currentDataFile, true);
                    bwPLFormat.OpenFile();

                    // Ensure that the first data point in the new file will start
                    // with the full, rather than differential, timecode info. 
                    isForceTimestampSave = true; 
                }
            }
        }

        int bytesFound;
        int someMITesDataIndex;

        /// <summary>
        /// Grab the data from the MITes Receiver Controller (serial port). 
        /// </summary>
        /// <param name="mrc"></param>
        public void GetSensorData(MITesReceiverController mrc)
        {
            bytesFound = mrc.FillBytesBuffer(mrc.serialBytesBuffer);
            if (bytesFound > 0)
            {
                //Debug("Bytes from fill: " + bytesFound);
                someMITesDataIndex = 0;
                someMITesDataIndex = aMITesDecoder.DecodeMITesData(mrc.serialBytesBuffer, bytesFound, aMITesDecoder.someMITesData, someMITesDataIndex);
            }
        }

        public void ShutdownFiles()
        {
            bwPLFormat.Flush();
            bwPLFormat.CloseFile();
          //  tw.Close();
        }

        private void WriteTimeStamp(int time, ByteWriter byteWriter)
        {
            if (isActive)
                byteWriter.WriteInt(time);
        }

        /// <summary>
        /// Completely turn on/off the logger.
        /// </summary>
        /// <param name="isActive">True if logging, false otherwise</param>
        public void SetActive(bool isActive)
        {
            this.isActive = isActive;
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

        private void SaveMITesData(MITesData aMITesData)
        {
            if (isActive && (bwPLFormat != null))
            {
                for (int i = 0; i < MITesData.MIN_NUM_RAW_BYTES; i++)
                {
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
                diffMS = (int) (aUnixTime -lastUnixTime);

                // Save a full timestamp if forced
                // or time is > than 255 ms
                if (isForceTimeCodeSave || (diffMS > 254))
                {
                    //if (diffMS >= 254)
                    //    Console.WriteLine("Warning; Max on MS diff: " + diffMS);
                    diffMSByte = (byte)255;
                    bwPLFormat.WriteByte(diffMSByte);
                    WriteTimeStampPLFormat(aUnixTime, bwPLFormat);
                }
                else // diff MS in range and no forced timestamp save
                {
                    diffMSByte = (byte)diffMS;
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
        //            //if (diffMS >= 254)
        //            //    Console.WriteLine("Warning; Max on MS diff: " + diffMS);
        //            diffMSByte = (byte)255;
        //            bwPLFormat.WriteByte(diffMSByte);
        //            WriteTimeStampPLFormat(unixTime, bwPLFormat);
        //        }
        //        else // diff MS in range and no forced timestamp save
        //        {
        //            diffMSByte = (byte)diffMS;
        //            bwPLFormat.WriteByte(diffMSByte);
        //        }
        //    }
        //}

        private int timeSaveCount = TIMESTAMP_AFTER_SAMPLES;
        private int aTime = 0;
        private double aUnixTime = 0;
        private int lastTime = 0;
        private double lastUnixTime = 0;
        private bool isForceTimestampSave = true; 

        
        //if you have MITes data only use this method
        public void SaveRawMITesBuiltinData(GenericAccelerometerData data)
        {
            if (isActive)
            {
                // Create and open the writer to the correct binary file in
                // the correct directory
                DetermineFilePath();

                //Store builtin data before the MITes data if it is timestamped before it
                if ((data != null) && (data.Unixtimestamp < aMITesDecoder.someMITesData[0].unixTimeStamp))
                    SaveRawBuiltinData(data);

                for (int i = 0; i < aMITesDecoder.someMITesDataIndex; i++)
                {
                    aTime = aMITesDecoder.someMITesData[i].timeStamp;
                    aUnixTime = aMITesDecoder.someMITesData[i].unixTimeStamp;       

                    if (aTime < lastTime)
                    {
                        Console.WriteLine("StepBack!: " + (lastTime-aTime));
                    }
                    if (aUnixTime < lastUnixTime)
                    {
                        Console.WriteLine("StepBackUnix!: " + (lastUnixTime - aUnixTime));
                    }

                    // Roughly once per second save full timestamp, no matter what
                    if (isForceTimestampSave || (timeSaveCount == TIMESTAMP_AFTER_SAMPLES))
                    {
                        //WriteTimeDiff(aTime, lastTime, aUnixTime, true); // Force save
                        WriteTimeDiff(aUnixTime, lastUnixTime, true); // Force save
                        timeSaveCount = 0;
                    }
                    else
                    {
                        //WriteTimeDiff(aTime, lastTime, aUnixTime, false);
                        WriteTimeDiff(aUnixTime, lastUnixTime, false);
                        timeSaveCount++;
                    }

                    isForceTimestampSave = false;

                    // Actually save the data! 
                    SaveMITesData(aMITesDecoder.someMITesData[i]);
                   // tw.WriteLine(aMITesDecoder.someMITesData[i].unixTimeStamp + ","+ aMITesDecoder.someMITesData[i].x + "," + aMITesDecoder.someMITesData[i].y + "," + aMITesDecoder.someMITesData[i].z);

                    lastTime = aTime;
                    lastUnixTime =aUnixTime; 
                }


                //Store builtin data after the MITes if it is stamped after the MITes data
                if ( (data != null) && (data.Unixtimestamp>=aMITesDecoder.someMITesData[0].unixTimeStamp))
                    SaveRawBuiltinData(data);                
            }
        }



    
        //if you have built in data only use this method
        public void SaveRawBuiltinData(GenericAccelerometerData data)
        {
            //lastUnixTime = 0;
            isForceTimestampSave = true;
            if (isActive)
            {
                // Create and open the writer to the correct binary file in
                // the correct directory
                DetermineFilePath();

                aTime = data.Timestamp;
                aUnixTime = data.Unixtimestamp;
                if (aTime < lastTime)
                {
                    Console.WriteLine("StepBack!: " + (lastTime - aTime));
                }
                if (aUnixTime < lastUnixTime)
                {
                    Console.WriteLine("StepBackUnix!: " + (lastUnixTime - aUnixTime));
                }

                // Roughly once per second save full timestamp, no matter what
                if (isForceTimestampSave || (timeSaveCount == TIMESTAMP_AFTER_SAMPLES))
                {
                    //WriteTimeDiff(aTime, lastTime, aUnixTime, true); // Force save
                    WriteTimeDiff(aUnixTime, lastUnixTime, true); // Force save
                    timeSaveCount = 0;
                }
                else
                {
                    //WriteTimeDiff(aTime, lastTime, aUnixTime, false);
                    WriteTimeDiff(aUnixTime, lastUnixTime, false);
                    timeSaveCount++;
                }

                isForceTimestampSave = false;

                // Actually save the data! 
                // SaveMITesData(aMITesDecoder.someMITesData[i]);

                if (isActive && (bwPLFormat != null))
                {
                    byte[] b = data.encode6Bytes();
                    for (int j = 0; j < b.Length; j++)
                    {
                        bwPLFormat.WriteByte(b[j]);
                    }
                }


                //tw.WriteLine(data.toString());

                lastTime = aTime;
                lastUnixTime = aUnixTime; 

            }



        }
    }
}
