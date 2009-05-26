using System;
using System.Diagnostics;
using System.Threading;
using System.IO;
using HousenCS.IO;
using Wockets;
using Wockets.Data;
using Wockets.Utils;



namespace Wockets.Data.Logger
{
    /// <summary>
    /// A MITesLoggerPLFormat saves MITes data into the binary PlaceLab format, with 
    /// timestamped filenames and directories (by hour).  
    /// </summary>
    public class PLFormatLogger
    {
        private ByteWriter bwPLFormat = null;
        private String currentDataFile = "";
        private bool isActive = true;
        private string aRootPathName = "";
        private WocketsController wocketsController;
        private int presentHour = -1;
        private string dayPath = "";
        public const string FILE_EXT = "b";
        public const string COMP_ID = "0";
        public const string FILE_TYPE_MONIKER = "MITesAccelBytes";

        public static int TIMESTAMP_AFTER_SAMPLES = 200;

        public PLFormatLogger(WocketsController controller, String aFilePath)
        {
            this.wocketsController = controller;
            aRootPathName = aFilePath;
            DetermineFilePath();
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

        public void ShutdownFiles()
        {
            bwPLFormat.Flush();
            bwPLFormat.CloseFile();
        }

        private void WriteTimeStamp(int time, ByteWriter byteWriter)
        {
            if (isActive)
                byteWriter.WriteInt(time);
        }


        public void SetActive(bool isActive)
        {
            this.isActive = isActive;
        }

        private byte[] retBytes = new byte[6];
        private void WriteTimeStampPLFormat(double unixTime, ByteWriter byteWriter)
        {
            if (isActive)
            {
                WocketsTimer.GetUnixTimeBytes(unixTime, retBytes);
                byteWriter.WriteBytes(retBytes, 6);
            }
        }


        private int diffMS = 0;
        private byte diffMSByte = 0;

        private void WriteTimeDiff(double aUnixTime, double lastUnixTime, bool isForceTimeCodeSave)
        {
            if (isActive)
            {
                diffMS = (int)(aUnixTime - lastUnixTime);

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



        private int timeSaveCount = TIMESTAMP_AFTER_SAMPLES;
        private double aUnixTime = 0;
        private double lastUnixTime = 0;
        private bool isForceTimestampSave = true;


        //if you have MITes data only use this method
        public void Save()
        {
            if (isActive)
            {
                // Create and open the writer to the correct binary file in
                // the correct directory
                DetermineFilePath();

                for (int i = 0; (i < this.wocketsController._Decoders.Count); i++)
                {
                    for (int j = 0; (j < this.wocketsController._Decoders[i]._Size); j++)
                    {
                        aUnixTime = this.wocketsController._Decoders[i]._Data[j].UnixTimeStamp;

                        if (aUnixTime < lastUnixTime)
                        {
                            Console.WriteLine("StepBackUnix!: " + (lastUnixTime - aUnixTime));
                        }

                        // Roughly once per second save full timestamp, no matter what
                        if (isForceTimestampSave || (timeSaveCount == TIMESTAMP_AFTER_SAMPLES))
                        {
                            WriteTimeDiff(aUnixTime, lastUnixTime, true); // Force save
                            timeSaveCount = 0;
                        }
                        else
                        {
                            WriteTimeDiff(aUnixTime, lastUnixTime, false);
                            timeSaveCount++;
                        }

                        isForceTimestampSave = false;

                        // Save Raw Bytes                        
                        if (bwPLFormat != null)
                            for (int k = 0; k < this.wocketsController._Decoders[i]._Data[j].NumRawBytes; k++)
                                bwPLFormat.WriteByte(this.wocketsController._Decoders[i]._Data[j].RawBytes[k]);

                        lastUnixTime = aUnixTime;
                    }
                }
            }
        }


    }
}
