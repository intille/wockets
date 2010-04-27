using System;
using System.Xml;
using System.Collections;
using System.IO;
using Wockets.Data.Accelerometers;
using Wockets.Sensors;
using Wockets.Decoders;
using Wockets.Receivers;
using Wockets.Utils;
using Wockets.Data.Configuration;
#if (PocketPC)
using Wockets.Utils.IPC.MMF;
#endif

namespace Wockets.Sensors.Accelerometers
{
    /// <summary>
    /// An abstract class that represents a 3-axis accelerometer and includes the main methods to process
    /// accelerometer data
    /// </summary>
    public abstract class Accelerometer : Sensor
    {

        #region Serialization Constants
        
        /// <summary>
        /// The XML element that stores calibration data
        /// </summary>
        protected const string CALIBRATION_ELEMENT = "CALIBRATION";
        
        /// <summary>
        /// The accelerometer range
        /// </summary>
        protected const string RANGE_ELEMENT = "RANGE";
        
        /// <summary>
        /// The maximum value of the accelerometer, 1023 for wockets
        /// </summary>
        protected const string MAX_ATTRIBUTE = "max";
        
        /// <summary>
        /// The minimum value of the accelerometer, 0 for wockets
        /// </summary>
        protected const string MIN_ATTRIBUTE = "min";

        /// <summary>
        /// The attribute for the x-axis accelerometer value at 1G
        /// </summary>
        protected const string X1G_ATTRIBUTE = "x1g";

        /// <summary>
        /// The attribute for the x-axis accelerometer value at -1G
        /// </summary>
        protected const string XN1G_ATTRIBUTE = "xn1g";

        /// <summary>
        /// The attribute for the y-axis accelerometer value at 1G
        /// </summary>
        protected const string Y1G_ATTRIBUTE = "y1g";

        /// <summary>
        /// The attribute for the y-axis accelerometer value at -1G
        /// </summary>
        protected const string YN1G_ATTRIBUTE = "yn1g";

        /// <summary>
        /// The attribute for the z-axis accelerometer value at 1G
        /// </summary>
        protected const string Z1G_ATTRIBUTE = "z1g";

        /// <summary>
        /// The attribute for the z-axis accelerometer value at -1G
        /// </summary>
        protected const string ZN1G_ATTRIBUTE = "zn1g";

        /// <summary>
        /// The attribute for the x-axis standard deviation
        /// </summary>
        protected const string XSTD_ATTRIBUTE = "xstd";

        /// <summary>
        /// The attribute for the y-axis standard deviation
        /// </summary>
        protected const string YSTD_ATTRIBUTE = "ystd";

        /// <summary>
        /// The attribute for the z-axis standard deviation
        /// </summary>
        protected const string ZSTD_ATTRIBUTE = "zstd";
        #endregion Serialization Constants

        #region calibration data
   
        /// <summary>
        /// The x axis value at 1G
        /// </summary>
        public double _X1g;

        /// <summary>
        /// The x axis value at -1G
        /// </summary>
        public double _Xn1g;

        /// <summary>
        /// The y axis value at 1G
        /// </summary>
        public double _Y1g;

        /// <summary>
        /// The y axis value at -1G
        /// </summary>
        public double _Yn1g;

        /// <summary>
        /// The z axis value at 1G
        /// </summary>
        public double _Z1g;

        /// <summary>
        /// The z axis value at -1G
        /// </summary>
        public double _Zn1g;

        /// <summary>
        /// The x axis standard deviation
        /// </summary>
        public double _XStd;

        /// <summary>
        /// The y axis standard deviation
        /// </summary>
        public double _YStd;

        /// <summary>
        /// The z axis standard deviation
        /// </summary>
        public double _ZStd;

        /// <summary>
        /// The minimum value on an axis
        /// </summary>
        public double _Min;

        /// <summary>
        /// The maximum value on an axis
        /// </summary>
        public double _Max;
        #endregion calibration data

        #region IO storage variables
        
        /// <summary>
        /// Specifies the current hour
        /// </summary>
        private int presentHour = -1;
        private int presentMinute = -1;
        private int presentSecond = -1;

        /// <summary>
        /// Specifies the storage path to the day
        /// </summary>
        private string dayPath = "";

        /// <summary>
        /// A reference to the current data writer
        /// </summary>
        private ByteWriter bw = null;

        /// <summary>
        /// The full path to the current data file
        /// </summary>
        private string currentDataFile = "";

        /// <summary>
        /// A prefix of the data file
        /// </summary>
        private const string FILE_TYPE_PREFIX = "WocketsAccelBytes";

        /// <summary>
        /// A suffix of the data file
        /// </summary>
        private const string FILE_EXT = "PLFormat";

        /// <summary>
        /// The maximum value between writing full timestamps to the file
        /// </summary>
        private static int TIMESTAMP_AFTER_SAMPLES = 200;

        /// <summary>
        /// A counter to determine the next time to save a full timestamp
        /// </summary>
        private int timeSaveCount = TIMESTAMP_AFTER_SAMPLES;

        /// <summary>
        /// Stores the current packet timestamp
        /// </summary>
        private double aUnixTime = 0;

        /// <summary>
        /// Stores the previous packet timestamp
        /// </summary>
        private double lastUnixTime = 0;

        /// <summary>
        /// True if a full timestamp need to be written
        /// </summary>
        private bool isForceTimestampSave = true;


        /// <summary>
        /// A counter that stores the time relative to the previous flush
        /// </summary>
        private int flushTimer = 0;        

        /// <summary>
        /// Specifies the maximum time between flushes
        /// </summary>
        private static int MAX_FLUSH_TIME = 2000;

        #endregion IO storage variables

        #region Memory Mapped File Definitions
#if (PocketPC)
        /// <summary>
        /// For shared memory mode, a reference to the memory mapped file associated with this sensor
        /// </summary>
        private MemoryMappedFileStream sdata = null;

        /// <summary>
        /// For shared memory mode, a reference to the file that stores the head pointer of the memory mapped file
        /// </summary>
        private MemoryMappedFileStream shead = null;

        /// <summary>
        /// Specifies the size in bytes of the data memory mapped file
        /// </summary>
        private int sdataSize = 0;

        /// <summary>
        /// A byte buffer to read the data pointer from the memory mapped file
        /// </summary>
        private byte[] head = new byte[4];
#endif
        #endregion Memory Mapped File Definitions


        #region File Storage Definitions

        private int diffMS = 0;
        private byte diffMSByte = 0;
        private byte[] retBytes = new byte[6];
        private int tail = 0;
        private double tailUnixTimestamp = 0;
        AccelerationData data = new WocketsAccelerationData();
        byte[] timestamp = new byte[sizeof(double)];
        byte[] acc = new byte[sizeof(short)];
        #endregion File Storage Definitions

        /// <summary>
        /// A constructor that intializes an accelerometer
        /// </summary>
        /// <param name="sensorclass">Specifies the class of the sensor (e.g. wocket, MITes)</param>
        public Accelerometer(SensorClasses sensorclass):base(SensorTypes.ACCEL,sensorclass)
        {
        }

        /// <summary>
        /// Releases any allocated resources and closes references to files
        /// </summary>
        public override void Dispose()
        {

#if (PocketPC)
            if (sdata != null)
                sdata.Close();
            if (shead != null)
                shead.Close();
#endif
            if (bw != null)
            {
                bw.Flush();
                bw.CloseFile();
            }

            if (br != null)            
                br.CloseFile();
            
        }


        /// <summary>
        /// Saves data to a binary file
        /// </summary>
        public override void Save()
        {
            int localflushtimer = 0;
#if (PocketPC)           
            if (_Saving)
            {

                #region Check if the data file need to be flushed
                /*flushTimer++;
                if ((flushTimer >= MAX_FLUSH_TIME) && (bw!=null))
                {
                    bw.Flush();
                    bw.CloseFile();
                    bw = new ByteWriter(currentDataFile, false);
                    bw.OpenFile(false);
                    flushTimer = 0;
                }*/
                #endregion Check if the data file need to be flushed

                #region Determine the head of the data buffer
                int currentHead = -1;
                if (CurrentWockets._Configuration._MemoryMode == MemoryConfiguration.SHARED)
                {
                    if (sdata == null)
                    {
                        this.sdataSize = (int)Decoder._DUSize * Wockets.Decoders.Accelerometers.WocketsDecoder.BUFFER_SIZE;
                        sdata = new MemoryMappedFileStream("\\Temp\\wocket" + this._ID + ".dat", "wocket" + this._ID, (uint)this.sdataSize, MemoryProtection.PageReadWrite);
                        shead = new MemoryMappedFileStream("\\Temp\\whead" + this._ID + ".dat", "whead" + this._ID, sizeof(int), MemoryProtection.PageReadWrite);

                        sdata.MapViewToProcessMemory(0, this.sdataSize);
                        shead.MapViewToProcessMemory(0, sizeof(int));
                        shead.Read(head, 0, 4);
                        int lastHead = BitConverter.ToInt32(head, 0);
                        tail = lastHead;
                        shead.Seek(0, System.IO.SeekOrigin.Begin);
                        sdata.Seek((lastHead * (sizeof(double) + 3 * sizeof(short))), System.IO.SeekOrigin.Begin);
                    }

                    shead.Read(head, 0, 4);
                    currentHead = BitConverter.ToInt32(head, 0);
                    shead.Seek(0, System.IO.SeekOrigin.Begin);
                }
                else
                    currentHead = this._Decoder._Head;
                #endregion Determine the head of the data buffer

                #region Check if a new binary file need to be created
                if (presentHour != DateTime.Now.Hour) //((bw==null)||(presentHour != DateTime.Now.Hour)|| (presentMinute != DateTime.Now.Minute) || (presentSecond!= DateTime.Now.Second))
                {
                    if (bw != null)
                        bw.CloseFile();
                    presentHour = DateTime.Now.Hour;
                    presentMinute = DateTime.Now.Minute;
                    presentSecond = DateTime.Now.Second;
                    // Need to create a new directory and switch the file name
                    dayPath = DirectoryStructure.DayDirectoryToUse(this._RootStorageDirectory);

                    // Make sure hour directory exists 
                    currentDataFile = dayPath + "\\" + presentHour + "\\";
                    if (!System.IO.Directory.Exists(currentDataFile))
                        System.IO.Directory.CreateDirectory(currentDataFile);

                    currentDataFile = currentDataFile + FILE_TYPE_PREFIX + "." +
                                   DirectoryStructure.GetDate() + "." + this._ID + "." + FILE_EXT;

                    bw = new ByteWriter(currentDataFile, true);
                    //bw.OpenFile();
                    bw.OpenFile(32768);

                    // Ensure that the first data point in the new file will start
                    // with the full, rather than differential, timecode info. 
                    isForceTimestampSave = true;
                }
                #endregion Check if a new binary file need to be created


                // Write data as long as the tail is not equal to the head
                while (tail != currentHead)
                {
                    #region Populate the acceleration data that need to be written
                    if (CurrentWockets._Configuration._MemoryMode == MemoryConfiguration.SHARED)
                    {
                        sdata.Read(timestamp, 0, sizeof(double));
                        data.UnixTimeStamp = BitConverter.ToDouble(timestamp, 0);
                        sdata.Read(acc, 0, sizeof(short));
                        data.X = BitConverter.ToInt16(acc, 0);
                        sdata.Read(acc, 0, sizeof(short));
                        data.Y = BitConverter.ToInt16(acc, 0);
                        sdata.Read(acc, 0, sizeof(short));
                        data.Z = BitConverter.ToInt16(acc, 0);
                    }
                    else
                        data = ((AccelerationData)this._Decoder._Data[tail]);
                    #endregion Populate the acceleration data that need to be written

                    #region Check for timestamp errors
                    aUnixTime = data.UnixTimeStamp;
                    if (aUnixTime < lastUnixTime)
                    {      
                        Logger.Error("Accelerometer: Save: Data overwritten without saving Accelerometer.cs Save " + this._ID + " " + aUnixTime + " " + lastUnixTime);
                        break;
                    }
                    #endregion Check for timestamp errors

                    #region Write Data
                    if (bw != null)
                    {
                        
                        #region Write Timestamp
                        diffMS = (int)(aUnixTime - lastUnixTime);
                        if (isForceTimestampSave || (diffMS > 254) || (timeSaveCount == TIMESTAMP_AFTER_SAMPLES))
                        {
                           
                            bw.WriteByte((byte)255);
                            WocketsTimer.GetUnixTimeBytes(aUnixTime, retBytes);
                            bw.WriteBytes(retBytes, 6);
                            timeSaveCount = 0;
                            isForceTimestampSave = false;
                        }
                        else
                        {
                            bw.WriteByte((byte)diffMSByte);
                            timeSaveCount++;
                        }
                        #endregion Write Timestamp

                        #region Write Raw Data
                        for (int j = 0; j < data.NumRawBytes; j++)
                            bw.WriteByte(data.RawBytes[j]);
                        #endregion Write Raw Data
                        /*

                        bw.WriteBytes(ttt);
                        this._SavedPackets = 2400;
                        tail = currentHead;
                        if (tail ==0)
                            data = ((AccelerationData)this._Decoder._Data[this._Decoder._Data.Length - 1]);
                        else
                            data = ((AccelerationData)this._Decoder._Data[tail - 1]);
                        aUnixTime = data.UnixTimeStamp;
                        break;      
                         */
                        
                       /* if ((this._Flush) && (localflushtimer > 200))
                        {                           
                            bw.Flush();
                           // bw.CloseFile();
                            //bw = new ByteWriter(currentDataFile, false);
                            //bw.OpenFile(false);
                            localflushtimer = 0;
                        }
                        else
                            localflushtimer++;*/
                         
                    }
                    #endregion Write Data


                   
                   
                    #region Update Pointers, statistics and time stamps
                    lastUnixTime = aUnixTime;
                    this.tailUnixTimestamp = aUnixTime;    
                    if (tail >= this._Decoder._Data.Length - 1)
                    {
                        tail = 0;
                        if (CurrentWockets._Configuration._MemoryMode == MemoryConfiguration.SHARED)
                            sdata.Seek(0, System.IO.SeekOrigin.Begin);
                    }
                    else
                        tail++;
                    this._SavedPackets++;
                    #endregion Update Pointers, statistics and time stamps

                }

                if ((bw != null) && (this._Flush))
                {
                    bw.Flush();
                    //bw.CloseFile();
                    //bw = null;
                    //bw = new ByteWriter(currentDataFile, false);
                    //bw.OpenFile(false);
                }           
            }
#endif
        }

        ArrayList someBinaryFiles = new ArrayList();
        private ByteReader br;

        /// <summary>
        /// Generates a list of binary files to load the data from
        /// </summary>
        private void GenerateBinaryFileList()
        {

            if (Directory.Exists(this._RootStorageDirectory) == false)
                return;

            string[] subdirectories = Directory.GetDirectories(this._RootStorageDirectory);
            foreach (string subdirectory in subdirectories)
            {
                for (int i = 0; i < 30; i++)
                {
                    if (Directory.Exists(subdirectory + "\\" + i))
                    {
                        string[] matchingFiles = Directory.GetFiles(subdirectory + "\\" + i, FILE_TYPE_PREFIX + "*" + this._ID + "." + FILE_EXT);
                        for (int j = 0; (j < matchingFiles.Length); j++)
                            someBinaryFiles.Add(matchingFiles[j]);
                    }
                }
            }
        }


        /// <summary>
        /// Sets up the next binary file to read the data from
        /// </summary>
        /// <param name="index"></param>
        /// <returns></returns>
        private bool SetupNextFiles(int index)
        {

            if (br != null)
                br.CloseFile();

            br = null;
            string f = ((string)someBinaryFiles[index]);

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

        private bool loading = false;
        private int fileIndex = 0;
        private byte[] b6 = new byte[6];
        private byte[] b = new byte[1];
        
        /// <summary>
        /// Loads one data packet at a time
        /// </summary>
        /// <returns>true if data is loaded, otherwise false</returns>
        public override bool Load()
        {
            //double lastUnixTime = aLastUnixTime; 
            //Generate the list of files to go through for this sensor
            if (loading == false)
            {
                GenerateBinaryFileList();
                if (someBinaryFiles.Count < 1)
                    return false;
                    //throw new Exception("Error: no PLFormat files for sensor " + this._ID);
                SetupNextFiles(0);
                loading = true;
            }

            while (true)
            {
                try
                {
                    #region Read Timestamp
                    if (!(br.ReadByte(b)))
                        throw new Exception("Error: reading first byte in PLFormat file");

                    //read a complete timestamp
                    if (b[0] == ((int)255))
                    {
                        if (!(br.ReadBytes(b6)))
                            throw new Exception("Error: reading full timestamp in PLFormat file");

                        lastUnixTime = WocketsTimer.DecodeUnixTimeCodeBytesFixed(b6);
                    }
                    else //read a differential timestamp          
                        lastUnixTime += (int)b[0];

                    #endregion Read Timestamp

                    DateTime dt = new DateTime();
                    WocketsTimer.GetDateTime((long)lastUnixTime, out dt);

                    int numRawBytes = 0;
                    if (this._Decoder._Type == DecoderTypes.Wockets)
                        numRawBytes = Data.Accelerometers.WocketsAccelerationData.NUM_RAW_BYTES;
                    else if (this._Decoder._Type == DecoderTypes.HTCDiamondTouch)
                        numRawBytes = Data.Accelerometers.HTCDiamondTouchAccelerationData.NUM_RAW_BYTES;

                    byte[] tempByte = new byte[numRawBytes];
                    if (!(br.ReadBytes(tempByte)))
                        throw new Exception("Error: reading data in PLFormat file");

       
                    int lastDecodedIndex = 0;
                    //Successfully decoded a packet
                    if (this._Decoder.Decode(this._ID, tempByte, tempByte.Length) == 1)
                    {

                        if (this._Decoder._Head == 0)
                            lastDecodedIndex = this._Decoder._Data.Length - 1;
                        else
                            lastDecodedIndex = this._Decoder._Head - 1;                        
                        this._Decoder._Data[lastDecodedIndex].UnixTimeStamp = lastUnixTime;                       
                        break;
                    }
                    else //failed to decode a packet... check if this ever happens
                        return false;
                }
                catch (Exception)
                {
                    //if the data ended return false
                    if (!((++fileIndex < someBinaryFiles.Count) && SetupNextFiles(fileIndex)))
                        return false;
                }
            }

            return true;
        }

        protected string ToXML(string innerXML)
        {
            innerXML += "<" + CALIBRATION_ELEMENT + " " + X1G_ATTRIBUTE +
                "=\"" + this._X1g.ToString("0.00") + "\" " + XN1G_ATTRIBUTE + "=\"" + this._Xn1g.ToString("0.00") +
                "\" " + Y1G_ATTRIBUTE + "=\"" + this._Y1g.ToString("0.00") + "\" " +
                YN1G_ATTRIBUTE + "=\"" + this._Yn1g.ToString("0.00") + "\" " +
                Z1G_ATTRIBUTE + "=\"" + this._Z1g.ToString("0.00") + "\" " +
                ZN1G_ATTRIBUTE + "=\"" + this._Zn1g.ToString("0.00") + "\" " +
                XSTD_ATTRIBUTE + "=\"" + this._XStd.ToString("0.00") + "\" " +
                YSTD_ATTRIBUTE + "=\"" + this._YStd.ToString("0.00") + "\" " +
                ZSTD_ATTRIBUTE + "=\"" + this._ZStd.ToString("0.00") + "\" />\n";
            innerXML += "<" + RANGE_ELEMENT + " " + MAX_ATTRIBUTE +
                "=\"" + this._Max.ToString("0.00") + "\" " + MIN_ATTRIBUTE + "=\"" + this._Min.ToString("0.00") + "\" />\n";
            return base.ToXML(innerXML);
        }

        /// <summary>
        /// Loads an accelerometer object from an XML string
        /// </summary>
        /// <param name="xml">An XML string that defines an accelerometer</param>
        public override void FromXML(string xml)
        {
            base.FromXML(xml);
            XmlDocument dom = new XmlDocument();
            dom.LoadXml(xml);
            XmlNode iNode = dom.DocumentElement;
            if (iNode.Name == SENSOR_ELEMENT)
            {
                foreach (XmlNode jNode in iNode.ChildNodes)
                {
                    foreach (XmlAttribute jAttribute in jNode.Attributes)
                    {                     
                        if ((jNode.Name == CALIBRATION_ELEMENT) && (jAttribute.Name == X1G_ATTRIBUTE))
                            this._X1g = Convert.ToDouble(jAttribute.Value);
                        else if ((jNode.Name == CALIBRATION_ELEMENT) && (jAttribute.Name == XN1G_ATTRIBUTE))
                            this._Xn1g= Convert.ToDouble(jAttribute.Value);
                        else if ((jNode.Name == CALIBRATION_ELEMENT) && (jAttribute.Name == Y1G_ATTRIBUTE))
                            this._Y1g = Convert.ToDouble(jAttribute.Value);
                        else if ((jNode.Name == CALIBRATION_ELEMENT) && (jAttribute.Name == YN1G_ATTRIBUTE))
                            this._Yn1g = Convert.ToDouble(jAttribute.Value);
                        else if ((jNode.Name == CALIBRATION_ELEMENT) && (jAttribute.Name == Z1G_ATTRIBUTE))
                            this._Z1g = Convert.ToDouble(jAttribute.Value);
                        else if ((jNode.Name == CALIBRATION_ELEMENT) && (jAttribute.Name == ZN1G_ATTRIBUTE))
                            this._Zn1g = Convert.ToDouble(jAttribute.Value);
                        else if ((jNode.Name == CALIBRATION_ELEMENT) && (jAttribute.Name == XSTD_ATTRIBUTE))
                            this._XStd = Convert.ToDouble(jAttribute.Value);
                        else if ((jNode.Name == CALIBRATION_ELEMENT) && (jAttribute.Name == YSTD_ATTRIBUTE))
                            this._YStd = Convert.ToDouble(jAttribute.Value);
                        else if ((jNode.Name == CALIBRATION_ELEMENT) && (jAttribute.Name == ZSTD_ATTRIBUTE))
                            this._ZStd = Convert.ToDouble(jAttribute.Value);
                        else if ((jNode.Name == RANGE_ELEMENT) && (jAttribute.Name == MIN_ATTRIBUTE))
                            this._Min = Convert.ToDouble(jAttribute.Value);
                        else if ((jNode.Name == RANGE_ELEMENT) && (jAttribute.Name == MAX_ATTRIBUTE))
                            this._Max = Convert.ToDouble(jAttribute.Value);

                    }
                }
            }
        }

    }
}

