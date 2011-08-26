using System;
using System.IO;
using System.Threading;
using HousenCS.IO;
using HousenCS.MITes;

namespace HousenCS.MITes
{
	/// <summary>
	/// Summary description for MITesRawLogger.
	/// </summary>
	public class MITesRawLogger
	{
		private FileWriter fw; 
		private double sampleTime;
	    private int[] channels;
	    private bool[] isSampFilled;  
        private int[] sx;
        private int[] sy;
        private int[] sz;

        private int[] sxNonZero;
        private int[] syNonZero;
        private int[] szNonZero;

        private int numChannels = 0;
	    private MITesDecoder aMITesDecoder;
        private short ID = (short)MITesData.NONE;

	    private string fileName; 
	    private int fileNum = 0; 
	    private const int SPLIT_LINES = 30000;  

		/// <summary>
		/// String saved to logfile when there is no data to report
		/// </summary>
		public static readonly string NONE_STRING = "0";
		
		/// <summary>
        /// Ceate an object that will save raw accelerometer data in a csv format. 
		/// </summary>
        public MITesRawLogger(MITesDecoder aMITesDecoder, string aFileName, int[] channels)
		{
		    this.aMITesDecoder = aMITesDecoder; 

			SetupFiles(aFileName);
		    this.channels = channels;
		    numChannels = channels.Length;

		    WriteKey();

            sx = new int[numChannels];
            sy = new int[numChannels];
            sz = new int[numChannels];

            sxNonZero = new int[numChannels];
            syNonZero = new int[numChannels];
            szNonZero = new int[numChannels];

            isSampFilled = new bool[numChannels];
            ClearSample();
        }

        private int GetIndex(int channel)
        {
            for (int i = 0; i < channels.Length; i++)
                if (channels[i] == channel)
                    return i;
            return -1;
        }

        private void ClearSample()
        {
            for (int i = 0; i < numChannels; i++)
            {
                sx[i] = 0; 
                sy[i] = 0; 
                sz[i] = 0;
                isSampFilled[i] = false;
            }
            sampleTime = 0; 
        }

	    private static int writeCount = 0; 
        /// <summary>
        /// 
        /// </summary>
        /// <param name="str"></param>
        public void WriteDataLine(String str)
        {
//            fw.OpenFile(false);
            fw.WriteLine(str);
            writeCount++; 

            if (writeCount == 200)
                fw.Flush();
        }

        /// <summary>
        /// 
        /// </summary>
        public void ShutDown()
        {
            SaveSampleLine(); 

            if (fw != null)
                fw.CloseFile();
        }

        /// <summary>
        /// 
        /// </summary>
        public void WriteKey()
        {
            string line = "TIMECODE,DATE"; 
            for (int i = 0; i < channels.Length; i++)
            {
                line += ", ACCEL " + channels[i] + "x";
                line += ", ACCEL " + channels[i] + "y";
                line += ", ACCEL " + channels[i] + "z";
            }
            WriteDataLine(line);
        }

        private void SetupFiles(String logFileName)
		{
            fileName = logFileName; 

            fileNum++;
            if (fw != null)
                fw.CloseFile();
            fw = null; 

            fw = new FileWriter(logFileName + fileNum + ".csv", false);
            fw.OpenFile(true);
		}

        private void SetupFiles()
        {
            SetupFiles(fileName);
        }

	    private static DateTime dt = new DateTime();
		/// <summary>
		/// 
		/// </summary>
		public void SaveSampleLine()
		{
            if (sampleTime == 0)
                return; 

		    string line = sampleTime.ToString();

		    UnixTime.GetDateTime((long)sampleTime, out dt);
		    line += "," + dt.ToString();

            for (int i = 0; i < numChannels; i++)
            {
                if (sx[i] == 0)
                    line += ","; 
                else
                    line += "," + sx[i];
                if (sy[i] == 0)
                    line += ",";
                else
                    line += "," + sy[i];
                if (sz[i] == 0)
                    line += ",";
                else
                    line += "," + sz[i];


                    //if (sx[i] == 0)
                    //    line += "," + sxNonZero[i];
                    //else
                    //    line += "," + sx[i];
                    //if (sy[i] == 0)
                    //    line += "," + syNonZero[i];
                    //else
                    //    line += "," + sy[i];
                    //if (sz[i] == 0)
                    //    line += "," + szNonZero[i];
                    //else
                    //    line += "," + sz[i];
            }
            WriteDataLine(line);

            if (writeCount > SPLIT_LINES)
            {
                writeCount = 0;
                SetupFiles();
            }

            ClearSample();
		}

        /// <summary>
        /// Check for samples and write out to raw log file as appropriate
        /// </summary>
        public void Update()
        {
            for (int i = 0; i < aMITesDecoder.someMITesDataIndex; i++)
            {
                if (aMITesDecoder.someMITesData[i].type == (int)MITesTypes.ACCEL)
                {
                    if ((ID == MITesData.NONE) ||
                        (ID == aMITesDecoder.someMITesData[i].id))
                    {
                        AddSample(aMITesDecoder.someMITesData[i]); 
                    }
                }
            }
        }

        private void AddSample(MITesData aMITesData)
        {
            int channel = aMITesData.channel;
            double unixTimeStamp = aMITesData.unixTimeStamp;
            int indx = GetIndex(channel);

            if (indx == -1)
            {
                Console.WriteLine("ERROR: Got an invalid channel number for an accelerometer: " + channel);
                return;
            }

            if (((unixTimeStamp - sampleTime) > 330) ||  // More than 330 ms so save previous 
                (isSampFilled[indx]))    // Already have this sensor value so start new
            {
                SaveSampleLine(); 
                sampleTime = unixTimeStamp; 
            }

            if (sampleTime == 0)
                sampleTime = unixTimeStamp;

            sx[indx] = aMITesData.x;
            sy[indx] = aMITesData.y;
            sz[indx] = aMITesData.z;
            isSampFilled[indx] = true;

            if (aMITesData.x != 0)
                sxNonZero[indx] = aMITesData.x;
            if (aMITesData.y != 0)
                syNonZero[indx] = aMITesData.y;
            if (aMITesData.z != 0)
                szNonZero[indx] = aMITesData.z;
        }
    }
}