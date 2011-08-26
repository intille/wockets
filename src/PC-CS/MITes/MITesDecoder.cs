using System;
using System.Threading;
using HousenCS.IO;
using System.IO;
#if (PocketPC)
using Bluetooth;
#endif

namespace HousenCS.MITes
{
    /// <summary>
    /// An object that takes raw data from the MITes receiver and converts it into a 
    /// collection of MITesData objects
    /// that can be more easily processed by other classes. The MITesDecoder stores 
    /// the raw and processed data and
    /// is the primary object used to access the data from other classes. It can also 
    /// compute the sampling rate of incomming valid MITes data. 
    /// </summary>
    public class MITesDecoder
    {
        /// <summary>
        /// Because of a bug in early transmitter code, bytes on non-accelerometer devices must 
        /// be swapped. To get this to happen, set this to true. Hopefully this will not be 
        /// needed soon. 
        /// </summary>
        public static readonly bool SWAP_BYTES = false;

        /// <summary>
        /// Last UnixTime of any data decoded 
        /// </summary>
        public double lastUnixTime = 0;

        /// <summary>
        /// The channel number that is used for all the non-accelerometer data, such as HR, beacons, light, UV, etc.  
        /// </summary>
        public static readonly int STATIC_CHANNEL = 0;

        /// <summary>
        /// The marker used to indicate each new set of receiver data (two PACKET_MARKERS in a row).
        /// </summary>
        public static readonly int PACKET_MARKER = 68;

        /// <summary>
        /// The byte size of each packet from the receiver. 
        /// </summary>
        public static readonly int MAX_PACKET_SIZE = 6;
        public static readonly int MIN_PACKET_SIZE = 5;
        public static readonly int WOCKET_PACKET_SIZE = 7;
        public static readonly int SPARKFUN_PACKET_SIZE = 15;

        public static readonly int MITES_SENSOR = 0;
        public static readonly int WOCKETS_SENSOR = 1;
        public static readonly int SPARKFUN_SENSOR = 2;

        /// <summary>
        /// The maximum valid channel that the receiver can use.  
        /// </summary>
        public static readonly int MAX_CHANNEL = 83;

        private static readonly int NO_HEADER_SEEN = -9;
        private static readonly int FIRST_HEADER_SEEN = -10;
        private int packetPosition = NO_HEADER_SEEN;
        private int x, y, z, xyz,xyz2;

        /// <summary>
        /// Storage for packet to be decoded. 
        /// </summary>
        public byte[] packet = new byte[MAX_PACKET_SIZE];
        public byte[] packet2 = new byte[WOCKET_PACKET_SIZE];
        public byte[] packet3 = new byte[SPARKFUN_PACKET_SIZE];
        public int packet2Position = 0;
        public int packet3Position = 0;
        private int v = 0;
        private int lV = 0;
        private static bool DEBUG = false;

        /// <summary>
        /// The maximum amount of MITes data that will be stored by this object. This
        /// has an impact on storage space and therefore is ideally kept smaller for 
        /// mobile devices. The code should issue warnings when this value is exceeded.
        /// </summary>
        public static readonly int MAX_MITES_DATA = 600; //Best not to rely on this and set in constructor

        /// <summary>
        /// Storage of the most recent MITesData computed from the serial port data. 
        /// </summary>
        public MITesData[] someMITesData;

        /// <summary>
        /// Storage of the most recent MITesData computed from the serial port data used when merging data from two receivers 
        /// </summary>
        public MITesData[] someMITesDataMerged;

        /// <summary>
        /// Current index for someMITesData (indicating the amount of new data). 
        /// </summary>
        public int someMITesDataIndex = 0;

        /// <summary>
        /// Returns the MITesData array, which is the main storage place for any newly 
        /// processed data.
        /// </summary>
        /// <returns></returns>
        public MITesData[] GetSomeMITesData()
        {
            return someMITesData;
        }

        /// <summary>
        /// Return the currently valid max index value for the MITesData array. 
        /// </summary>
        /// <returns></returns>
        public int GetSomeMITesDataIndex()
        {
            return someMITesDataIndex;
        }

        /// <summary>
        /// Create an object to process incoming serial port data and convert it 
        /// into a useful MITesData format that can be processed by many classes.
        /// Defaults to a maximum number of data objects of MAX_MITEs_DATA.
        /// </summary>
        public MITesDecoder()
            : this(MAX_MITES_DATA)
        { }

        private System.IO.TextWriter tw;
        /// <summary>
        /// reate an object to process incoming serial port data and convert it 
        /// into a useful MITesData format that can be processed by many classes.
        /// </summary>
        /// <param name="maxMITesData">The maximum number of MITesData objects that can be stored. If this is too small, data will be lost. Too large, and mobile devices may run out of storage or run slowly.</param>
        public MITesDecoder(int maxMITesData)
        {
            someMITesData = new MITesData[maxMITesData];
            someMITesDataMerged = new MITesData[maxMITesData];

            // All datastructures created in advance, so value of maxMITesData impacts storage,
            // but the amount of space used will be consistent.
            for (int i = 0; i < someMITesData.Length; i++)
                someMITesData[i] = new MITesData();
            
        }

        private void Debug(String aMsg)
        {
            if (DEBUG)
                Console.WriteLine("DEBUG: " + aMsg);
        }

        private void Warning(String aMsg)
        {
            Console.WriteLine("Warning: " + aMsg);
        }

        private int bytesFound = 0;
        private long sampleTime = Environment.TickCount;
        private int sampleCount = 0;
        private int sampleCountUpdateCount = 0;
        private int sampleRate = 0;
        private int lastSamplingRateComputed = 0;

        /// <summary>
        /// Return the last sampling rate computed by the MITesDecoder. Does not force 
        /// computation of the value. 
        /// </summary>
        /// <returns>The sampling rate in MITesData/sec</returns>
        //public int GetLastSamplingRateComputed()
        //{
        //    return lastSamplingRateComputed;
        //}

        /// <summary>
        /// Computes the sampling rate of incoming MITesData (forces the computation to
        /// occur). UpdateSamplingRate must be called from the main data processing loop
        /// after each new data is processed in order for this to return valid values!   
        /// </summary>
        /// <returns>The sampling rate in MITesData/sec.</returns>
        public int GetSamplingRate()
        {
            ComputeSamplingRate();
            sampleCountUpdateCount = 0;
            lastSamplingRateComputed = sampleRate;
            return sampleRate;
        }

        // Compute the sampling rate since last time called
        private void ComputeSamplingRate()
        {
            double dt = (Environment.TickCount - sampleTime) / 1000.0; // seconds			

            if (sampleCount == 0)
                sampleRate = 0;
            else
                sampleRate = (int)Math.Floor(sampleCount / dt);
            sampleTime = Environment.TickCount;
            sampleCount = 0;
        }

        /// <summary>
        /// Called from the main data processing loop after each time new data is grabbed/processed.
        /// This updates the sampling rate. As a default, it is good to do this, but it can be 
        /// removed from the main loop or only used occasionally to pick up a tiny bit of speed. 
        /// If this is not called regularly, GetSamplingRate won't work!
        /// </summary>
        /// <param name="numSamples"></param>
        public void UpdateSamplingRate(int numSamples)
        {
            //Console.WriteLine ("Num samp: " + numSamples);
            sampleCount += numSamples;
            sampleCountUpdateCount++;

            if (sampleCountUpdateCount > 1000)
            {
                GetSamplingRate();
                //Console.WriteLine ("Sampling rate per sec: " + GetSamplingRate());
                sampleCountUpdateCount = 0;
            }
        }

        //private int byteSum = 0;
        //private int lastByteNumGrabbed = 0;
        //private int startTime = Environment.TickCount;
        //private double timePer300Bytes = 0.0;
        //private void UpdateDataRate(int n)
        //{
        //    lastByteNumGrabbed = n;
        //    byteSum += n;
        //    if (byteSum >= 300)
        //    {
        //        timePer300Bytes = (Environment.TickCount - startTime) / 1000.0;
        //        startTime = Environment.TickCount;
        //        byteSum = 0;
        //    }
        //}

        ///// <summary>
        ///// 
        ///// </summary>
        ///// <returns></returns>
        //public int GetLastByteNum()
        //{
        //    return lastByteNumGrabbed;
        //}


        /// <summary>
        /// Return the time it takes to read 300 bytes off the serial port.
        /// </summary>
        /// <returns>The time in milliseconds</returns>
        //public double GetTimePer300Bytes()
        //{
        //    return timePer300Bytes;
        //}

        /// <summary>
        /// Merge the recovered MITes data from two MITesDecoder objects. Adding the data from the decoder
        /// sent as the argument to this decoder. 
        /// </summary>
        /// <param name="aMITesDecoderToMerge">Merge and clear data from this MITesDecoder</param>
        public void MergeData(MITesDecoder aMITesDecoderToMerge)
        {
            //Console.WriteLine("M: " + aMITesDecoderToMerge.someMITesDataIndex + "+" + someMITesDataIndex);
            for (int i = 0; i < aMITesDecoderToMerge.someMITesDataIndex; i++)
            {
                someMITesData[someMITesDataIndex] = aMITesDecoderToMerge.someMITesData[i];
                someMITesDataIndex++;
            }

            aMITesDecoderToMerge.someMITesDataIndex = 0;
        }

        /// <summary>
        /// Merge the recovered MITes data from two MITesDecoder objects. Adding the data from the decoder
        /// sent as the argument to this decoder. This ensures that the order is correct based on timestamps. 
        /// </summary>
        /// <param name="aMITesDecoderToMerge">Merge and clear data from this MITesDecoder</param>
        public void MergeDataOrderProperly(MITesDecoder aMITesDecoderToMerge)
        {
            //Console.WriteLine("M: " + aMITesDecoderToMerge.someMITesDataIndex + "+" + someMITesDataIndex);
            for (int i = 0; i < aMITesDecoderToMerge.someMITesDataIndex; i++)
            {
                if (someMITesDataIndex < someMITesData.Length)
                {
                    // Swap the info from the aMITesDecoderToMerge object into the current someMITesData object. This is a 
                    // destructive operation for the aMITesDecoderToMerge object. Don't try to use that data anymore! 
                    MITesData tmp = someMITesData[someMITesDataIndex];
                    someMITesData[someMITesDataIndex] = aMITesDecoderToMerge.someMITesData[i];
                    aMITesDecoderToMerge.someMITesData[i] = tmp;
                    someMITesDataIndex++;
                }
                else
                {
                    Console.WriteLine("Losing data in merge");
                    break;
                }
            }
            aMITesDecoderToMerge.someMITesDataIndex = 0;
            Array.Sort(someMITesData, 0, someMITesDataIndex);
        }

        /// <summary>
        /// Print the list of channels in the someMITesData object in order for debugging
        /// </summary>
        public void PrintChannels()
        {
            for (int i = 0; i < someMITesDataIndex; i++)
                Console.Write(" " + someMITesData[i].channel);
            Console.WriteLine();
        }

        /// <summary>
        /// Check if invalid channel on receiver
        /// </summary>
        public bool IsWrongChannel(int chan)
        {
            for (int i = 0; i < someMITesDataIndex; i++)
                if (someMITesData[i].channel != chan)
                    return true;
            return false;
        }


#if (PocketPC)
        int byteCounter = 0;
        int calls = 0;
        /// <summary>
        /// This is the call that needs to be included in the main data processing loop to get
        /// data from a Bluetooth stream.
        /// </summary>
        /// <param name="bs"></param>
        public void GetSensorData(BluetoothController btc,int type)
        {
            calls++;
            bytesFound = btc.read(btc.BluetoothBytesBuffer);
            byteCounter += bytesFound;
            if (calls >= 20)
            {
                calls = 0;
                if (byteCounter == 0)  
                    throw new Exception();
                
                byteCounter = 0;
            }
            //UpdateDataRate(bytesFound);
            if (bytesFound > 0)
            {
                Debug("Bytes from fill: " + bytesFound);
                someMITesDataIndex = 0;
                if (type==MITES_SENSOR)
                    someMITesDataIndex = DecodeMITesData(btc.BluetoothBytesBuffer, bytesFound, someMITesData, someMITesDataIndex);
                else if (type == WOCKETS_SENSOR)
                    someMITesDataIndex = DecodeWocketsData(btc.BluetoothBytesBuffer, bytesFound, someMITesData, someMITesDataIndex);
                else if (type == SPARKFUN_SENSOR)
                    someMITesDataIndex = DecodeSparkfunData(btc.BluetoothBytesBuffer, bytesFound, someMITesData, someMITesDataIndex);
            }
            else
            {
                someMITesDataIndex = 0;
            }
        }

#endif
        /// <summary>
        /// This is the call that needs to be included in the main data processing loop.
        /// It checks for new data on the MITesReceiverController. If it finds some, it 
        /// processes that data and stores any valid MITesData in the someMITesData 
        /// variable. That data can then be processed by various MITesAnalyzer classes. 
        /// </summary>
        /// <param name="mrc">The opened MITesReceiverController from which data is pulled.</param>
        public void GetSensorData(MITesReceiverController mrc)
        {
            //			if (mrc.IsNewData())
            //			{
            bytesFound = mrc.FillBytesBuffer(mrc.serialBytesBuffer);
            //UpdateDataRate(bytesFound);
            if (bytesFound > 0)
            {
                Debug("Bytes from fill: " + bytesFound);
                someMITesDataIndex = 0;
                someMITesDataIndex = DecodeMITesData(mrc.serialBytesBuffer, bytesFound, someMITesData, someMITesDataIndex);
            }
            else
            {
                someMITesDataIndex = 0;
            }
            //Thread.Sleep(0);
        }

        private void DecodeAccelerometerPacket(MITesData aMITesData)
        {
            Debug("Decode Accelerometer MITe sensor");

            aMITesData.channel = packet[0];
            //Console.WriteLine ("Channel: " + packet[0]);
            

            x = packet[1];
            y = packet[2];
            z = packet[3];
            xyz = packet[4];
      

            if (aMITesData.channel == MAX_CHANNEL)
            {
                xyz2 = packet[5];
                aMITesData.type = (byte)(xyz2 & 0x0F); 
                aMITesData.x = (short)(x | ((xyz & 0xF0) << 4));
                aMITesData.y = (short)(y | ((xyz & 0x0F) << 8));
                aMITesData.z = (short)(z | ((xyz2 & 0xF0) << 4));

            }
            else
            {
                aMITesData.type = (int)MITesTypes.ACCEL; // Type label used for Accelerometers
                aMITesData.x = (short)(x | ((xyz & 0xC0) << 2));
                aMITesData.y = (short)(y | ((xyz & 0x30) << 4));
                aMITesData.z = (short)(z | ((xyz & 0x0C) << 6));
            }

            //Debug(aMITesData.channel + ": x " + x + " y " + y + " z " + z);
            //Console.WriteLine(aMITesData.channel + ": x " + x + " y " + y + " z " + z);
        }

        private void DecodeGenericPacket(MITesData aMITesData)
        {
            aMITesData.sensorValue = (((packet[3] & 0xFF) << 3) | ((packet[4] & 0xE0) >> 5));
            aMITesData.resendID = (byte)((packet[4] & 0x1C) >> 2);

            if (((packet[4] & 0x02) >> 1) == 1)
                aMITesData.isBatteryLow = true;
            else
                aMITesData.isBatteryLow = false;

            if ((packet[4] & 0x01) == 1)
                aMITesData.isAlive = true;
            else
                aMITesData.isAlive = false;
        }

        private void DecodeSwitchPacket(MITesData aMITesData)
        {

            // A value of 512 indicates noise 

            aMITesData.type = (int)MITesTypes.STATIC;
            Debug("Decode static switch packet");

            aMITesData.sensorValue = (((packet[3] & 0xFF) << 1) | ((packet[4] & 0xE0) >> 7));
            aMITesData.recentActivationsValue = ((packet[4] & 0x60) >> 5);

            aMITesData.resendID = (byte)((packet[4] & 0x1C) >> 2);

            if (((packet[4] & 0x02) >> 1) == 1)
                aMITesData.isBatteryLow = true;
            else
                aMITesData.isBatteryLow = false;

            if ((packet[4] & 0x01) == 1)
                aMITesData.isAlive = true;
            else
                aMITesData.isAlive = false;

            //			Console.WriteLine("********************  Decode static switch packet");
            //			Console.WriteLine("********************  ID: " + aMITesData.id);
            //			Console.WriteLine("********************  Value: " + aMITesData.sensorValue);
            //			Console.WriteLine("********************  Activations: " + aMITesData.recentActivationsValue);
            //			Console.WriteLine("********************  Alive: " + aMITesData.isAlive);
            //			if (aMITesData.isAlive)
            //				Console.WriteLine("********************  Alive: " + aMITesData.isAlive);

        }

        private void DecodeHRPacket(MITesData aMITesData)
        {
            Debug("Decode HR packet");
            aMITesData.type = (int)MITesTypes.HR;
            DecodeGenericPacket(aMITesData);
        }

        private void DecodeUVPacket(MITesData aMITesData)
        {
            Debug("Decode UV packet");
            aMITesData.type = (int)MITesTypes.UV;
            DecodeGenericPacket(aMITesData);
        }

        private void DecodeCurrentTrainingPacket(MITesData aMITesData)
        {
            Debug("Decode Current TRAINING packet");
            Console.WriteLine("Decode Current TRAINING packet");

            //			aMITesData.sensorValue = (((packet[3] & 0xFF) << 3) | ((packet[4] & 0xE0) >> 5));
            //			aMITesData.resendID = (byte) ((packet[4] & 0x1C) >> 2);
            //
            //			if (((packet[4] & 0x02) >> 1) == 1)
            //				aMITesData.isBatteryLow = true;
            //			else
            //				aMITesData.isBatteryLow = false;
            //			
            //			if ((packet[4] & 0x01) == 1)
            //				aMITesData.isAlive = true;
            //			else
            //				aMITesData.isAlive = false;
        }

        private void DecodeCurrentPacket(MITesData aMITesData)
        {
            Debug("Decode Current packet");
            Console.WriteLine("Decode Current packet");
            aMITesData.type = (int)MITesTypes.CURRENT;

            // First check if packet from training mode. If so, special decode
            //			if ((aMITesData.rawBytes[4] & 0x400) == 0x400) 
            //			{
            //				DecodeCurrentTrainingPacket(aMITesData);
            //			}
            //			else
            DecodeGenericPacket(aMITesData);
        }

        private void DecodeRangePacket(MITesData aMITesData)
        {
            Debug("Decode Range Beacon packet");
            aMITesData.type = (int)MITesTypes.RANGE;
            DecodeGenericPacket(aMITesData);
        }

        private void DecodeLightPacket(MITesData aMITesData)
        {
            Debug("Decode light packet");
            aMITesData.type = (int)MITesTypes.LIGHT;
            DecodeGenericPacket(aMITesData);
        }

        private void DecodeTempPacket(MITesData aMITesData)
        {
            Debug("Decode temp packet");
            aMITesData.type = (int)MITesTypes.TEMP;
            DecodeGenericPacket(aMITesData);
        }

        private bool ISValidType(int id)
        {
            if ((id >= 0) && (id <= 16)) // Max of 16 types, see MITesData.Types
                return true;
            else
                return false;
        }

        private bool ISValidID(int id)
        {
            if (((id >= 0) && (id <= 1091)) ||
                ((id >= 1093) & (id <= 4096)))
                return true;
            else
                return false;
        }

        private int id = 0;
        private int type = 0;
        private void DecodeOtherPacket(MITesData aMITesData)
        {
            Debug("Decode non-accelerometer MITe sensor!");

            aMITesData.channel = packet[0];

            id = (((packet[1] & 0xFF) << 4) | ((packet[2] & 0xF0) >> 4));

            if (!ISValidID(id))
                Warning("Invalid ID: " + id);

            // SSI Check here ot ensure valid conversion?
            aMITesData.id = (short)id;

            type = (packet[2] & 0x0F);

            if (!ISValidType(type))
                Warning("Invalid Type: " + type);

            aMITesData.type = (byte)type;

            switch (type)
            {
                case ((int)MITesTypes.STATIC):
                    DecodeSwitchPacket(aMITesData);
                    break;
                case ((int)MITesTypes.LIGHT):
                    DecodeLightPacket(aMITesData);
                    break;
                case ((int)MITesTypes.RANGE):
                    DecodeRangePacket(aMITesData);
                    break;
                case ((int)MITesTypes.HR):
                    DecodeHRPacket(aMITesData);
                    break;
                case ((int)MITesTypes.CURRENT):
                    DecodeCurrentPacket(aMITesData);
                    break;
                case ((int)MITesTypes.UV):
                    DecodeUVPacket(aMITesData);
                    break;
                case ((int)MITesTypes.TEMP):
                    DecodeTempPacket(aMITesData);
                    break;
                case ((int)MITesTypes.IR):
                    break;
                default:
                    Warning("Unhandled MITesData type: " + type);
                    break;
            }
        }

        private bool IsAccelerometerChannel(int channel)
        {
            // Check channel is valid and not equal to STATIC_CHANNEL
            if ((channel >= 0) &&
                (channel != STATIC_CHANNEL) &&
                (channel <= MAX_CHANNEL))
                return true;
            else
                return false;
        }

        private bool IsValidChannel(int channel)
        {
            if ((channel >= 0) && (channel <= MAX_CHANNEL))
                return true;
            else
                return false;
        }

        private bool IsValidChannelSelective(int channel)
        {
            if ((channel >= 0) && (channel <= 17))
            {
               if (channel == 0)
                   return true;
                if (channel == 1)
                    return true;
                if (channel == 4)
                    return true;
                if (channel == 7)
                    return true;
                if (channel == 8)
                    return true;
                if (channel == 11)
                    return true;
                if (channel == 14)
                    return true;
                if (channel == 17)
                    return true;
                if (channel == 83)
                    return true;
                return false;
            }
            else
                return false;
        }

        // R
        /// <summary>
        /// Raw bytes are stored with each MITesData so data can be easily saved back out again in an 
        /// efficient format 
        /// </summary>
        /// <param name="aMITesData">The object in which to store the raw bytes.</param>
        private void SetRawBytes(MITesData aMITesData)
        {

            aMITesData.rawBytes[0] = packet[0];
            aMITesData.rawBytes[1] = packet[1];
            aMITesData.rawBytes[2] = packet[2];
            aMITesData.rawBytes[3] = packet[3];
            aMITesData.rawBytes[4] = packet[4];

            if (packet[0]==MITesDecoder.MAX_CHANNEL)
                aMITesData.rawBytes[5] = packet[5];
            else
                aMITesData.rawBytes[5] = 0;
           
            
           //System.IO.TextWriter tw = new System.IO.StreamWriter("C:\\Test\\test.txt", true);
            //tw.WriteLine("D: " + packet[0] + " " + packet[1] + " " + packet[2] + " " + packet[3] + " " + packet[4]);
            //tw.Close();
        }

        /// <summary>
        /// The time at which each MITesData object is decoded is recorded. 
        /// </summary>
        /// <param name="aMITesData">The object in which to store the time.</param>
        private void SetTime(MITesData aMITesData)
        {
            aMITesData.timeStamp = Environment.TickCount;
            //Console.WriteLine ("Settime: " + aMITesData.timeStamp);
        }



        /// <summary>
        /// The UNIX time at which each MITesData object is decoded is recorded. 
        /// </summary>
        /// <param name="aMITesData">The object in which to store the time.</param>
        public void SetUnixTime(MITesData aMITesData)
        {
            
            aMITesData.unixTimeStamp = UnixTime.GetUnixTime();
            //lastUnixTime = aMITesData.unixTimeStamp;
            //  QueryPerformanceCounter(out aMITesData.highPrecisionTime);
        }

        /// <summary>
        /// The UNIX time at which each MITesData object is decoded is recorded. 
        /// </summary>
        /// <param name="aMITesData">The object in which to store the time.</param>
        /// <param name="aTime">The time to use.</param>
        public void SetUnixTime(MITesData aMITesData, double aTime)
        {
            aMITesData.unixTimeStamp = aTime;
            lastUnixTime = aTime;
        }

        private byte temp = 0;


        /// <summary>
        /// 
        /// </summary>
        /// <param name="aMITesData"></param>
        /// <param name="isSwapBytes"></param>
        public void DecodeLastPacket(MITesData aMITesData, bool isSwapBytes)
        {
            aMITesData.ResetVals();

            Debug("Packet: " + packet[0]
                + " " + packet[1]
                + " " + packet[2]
                + " " + packet[3]
                + " " + packet[4]);

            if (packet[0] == STATIC_CHANNEL)
            {
                if (isSwapBytes)
                {
                    // This is a hack to fix the swap byte problem
                    temp = packet[2];
                    packet[2] = packet[1];
                    packet[1] = temp;
                    temp = packet[4];
                    packet[4] = packet[3];
                    packet[3] = temp;
                }

                SetRawBytes(aMITesData);
                DecodeOtherPacket(aMITesData);
                SetTime(aMITesData);
                SetUnixTime(aMITesData);

            }
            else if (IsAccelerometerChannel(packet[0]))
            {
                SetRawBytes(aMITesData);
                DecodeAccelerometerPacket(aMITesData);
                SetTime(aMITesData);
                SetUnixTime(aMITesData);
                
            }
            else
            {
                Warning("Invalid channel: " + packet[0]);
            }

            Debug("Data:" + aMITesData);
        }

        private void DecodeLastPacket(MITesData aMITesData)
        {
            DecodeLastPacket(aMITesData, SWAP_BYTES); // Default to swap bytes
        }
        //set the sync bit,no compession, length and channel
    //frame.byte1 |= 0xA8 | UNCOMPRESSED_LENGTH;
    //frame.byte2 |= (crc>>1);
    //frame.byte3 |= ((crc<<7)>>1) | ((unsigned char) ((x>>4)&0x3f));
    //frame.byte4 |=  ((unsigned char) ((x<<3) &0x78)) | ((unsigned char) ((y>>7)&0x07));
    //frame.byte5 |= ((unsigned char) (y&0x7f));
    //frame.byte6 |= ((unsigned char) ((z>>3)&0x7f));
    //frame.byte7 |= ((unsigned char) ((z<<4)&0x70));

        public void DecodeWocketsFrame(MITesData aMITesData,byte[] raw)
        {
            aMITesData.channel = (byte)((raw[0]&0x38)>>3);
            aMITesData.x= (short)((((short)(raw[2]&0x3f))<<4) | (((short)(raw[3]&0x78))>>3));
            aMITesData.y = (short)((((short)(raw[3] & 0x07)) << 7) | ((short)(raw[4] & 0x7f)));
            aMITesData.z = (short)((((short)(raw[5] & 0x7f)) << 3) | (((short)(raw[6] & 0x70)) >> 4));
            aMITesData.type = ((int)MITesTypes.ACCEL);
            SetTime(aMITesData);
            SetUnixTime(aMITesData);         
        }

        public void DecodeSparkfunFrame(MITesData aMITesData, byte[] raw)
        {
            aMITesData.channel = 26;
            aMITesData.x = (short)((((short)raw[4])<<8) | ((short)raw[5]));
            aMITesData.y = (short)((((short)raw[6]) << 8) | ((short)raw[7]));
            aMITesData.z = (short)((((short)raw[8]) << 8) | ((short)raw[9]));
            aMITesData.type = ((int)MITesTypes.ACCEL);
            SetTime(aMITesData);
            SetUnixTime(aMITesData);
        }

        public int DecodeSparkfunData(byte[] bytes, int numBytes, MITesData[] someData, int dataIndex)
        {
            int i = 0;
            int valuesGrabbed = 0;
            bool header_started = false;

            if (numBytes != 0) // Have some data
            {
                while (i < numBytes)
                {
                    if ((bytes[i])=='#') //grab the next 6 bytes
                    {
                        packet3Position = 0;
                        header_started = true;
                    }

                    if ((header_started == true) && (packet3Position < SPARKFUN_PACKET_SIZE))
                        packet3[packet3Position] = bytes[i];

                    packet3Position++;
                    i++;
                    if ((packet3Position == SPARKFUN_PACKET_SIZE) && (packet3[SPARKFUN_PACKET_SIZE-1]=='$')) //a full packet was received
                    {
                        DecodeSparkfunFrame(someData[dataIndex], packet3);
                        dataIndex++;
                        packet3Position = 0;
                        header_started = false;
                        valuesGrabbed++;
                    }
                }
            }

            if (valuesGrabbed < someData.Length)
                return valuesGrabbed;
            else
                return someData.Length;
        }


        TextWriter decoderlog=null;
        public int DecodeWocketsData(byte[] bytes, int numBytes, MITesData[] someData, int dataIndex)
        {
            int i = 0;
            int valuesGrabbed = 0;
            bool header_started=false;
            //if (decoderlog==null)
              //  decoderlog = new StreamWriter("\\Wockets\\decoding.txt",true);       
            if (numBytes != 0) // Have some data
            {
                while (i < numBytes)
                {                    
                    if ((bytes[i] & 0x80) != 0) //grab the next 6 bytes
                    {
                        packet2Position = 0;
                        header_started = true;
                    }
          
                    if ( (header_started==true) && (packet2Position<WOCKET_PACKET_SIZE))
                        packet2[packet2Position] = bytes[i];

                    packet2Position++;
                    i++;

                   /* if (dataIndex == MAX_MITES_DATA)
                    {
                        decoderlog.WriteLine("DataIndex: " +dataIndex);
                        decoderlog.Flush();
                    }*/
                    if ((packet2Position == WOCKET_PACKET_SIZE)) //a full packet was received
                    {
                        DecodeWocketsFrame(someData[dataIndex], packet2);
                        if (dataIndex<MAX_MITES_DATA-1)
                            dataIndex++;
                        packet2Position = 0;
                        header_started = false;
                        valuesGrabbed++;
                         
                    }
                    //else
                    //{
                     //   decoderlog.WriteLine("Overflow while decoding");
                    //}
                }
            }

            //decoderlog.WriteLine("Decoded: " + valuesGrabbed);
            //decoderlog.Flush();

            if (valuesGrabbed < someData.Length)
                return valuesGrabbed;
            else
                return someData.Length;
        }
        /// <summary>
        /// The main call to decode data grabbed from the serial port int MITesData objects.
        /// </summary>
        /// <param name="bytes">Incoming bytes from the serial port.</param>
        /// <param name="numBytes">Number of incoming bytes from the serial port.</param>
        /// <param name="someData">The array in which the resulting MITesData will be stored.</param>
        /// <param name="dataIndex">The current index of the array in which the MITesData will be stored. (This will append data onto the end of existing data if needed).</param>
        /// <returns>The new index for the someData array.</returns>
        public int DecodeMITesData(byte[] bytes, int numBytes, MITesData[] someData, int dataIndex)
        {
            int i = 0;
            int valuesGrabbed = 0;
            int variablePacketSize = MIN_PACKET_SIZE;

            //tw = new System.IO.StreamWriter("C:\\Test\\test.txt", true);

            //Console.WriteLine(" BB ");
            if (numBytes != 0) // Have some data
            {
                //tw.Write("(GOT DATA: " + numBytes + ")");
                //tw.Flush();
                while (i < numBytes)
                {
                    v = bytes[i] & 0xff;

                    //tw.Write("(" + i + ",v: " + v + ",LV: " + lV + ",PP: " + packetPosition + "," + dataIndex + ")" + " ");
                    //tw.Flush();

                    // First check if got a reset and start of packet
                    if ((packetPosition == NO_HEADER_SEEN) && (v == PACKET_MARKER))
                    {
                        packetPosition = FIRST_HEADER_SEEN;
                    }
                    // Any two markers in a row is *always* a packet. This will occasionally cause an error. 
                    else if ((v == PACKET_MARKER) && (lV == PACKET_MARKER))
                    {
                        packetPosition = 0;
                    }
                    // Must have seen header 
                    else if (packetPosition >= 0) // Must have seen header
                    {
                        packet[packetPosition] = bytes[i];

                        //set the size of the packet
                        if ((packetPosition == 0) && (IsValidChannelSelective(packet[packetPosition])))
                        {
                            if ((packet[packetPosition] == MAX_CHANNEL))
                                variablePacketSize = MAX_PACKET_SIZE;
                            else
                                variablePacketSize = MIN_PACKET_SIZE;
                        }

                        // Sanity check. Make sure channel is valid ... if not, reset and wait for new header
                        if ((packetPosition == 0) && (!IsValidChannelSelective(packet[packetPosition])))
                        {
                            if (v == PACKET_MARKER)
                              packetPosition = FIRST_HEADER_SEEN;
                            else
                              packetPosition = NO_HEADER_SEEN;

 

                        }
                        else
                        {
                            packetPosition++;
                            //if (packetPosition == PACKET_SIZE)
                            if (packetPosition == variablePacketSize)
                            {
                                if (dataIndex >= someData.Length)
                                {
                                    Warning("MAX_MITES_DATA too small! Losing info. Size:" + someData.Length);
                      //              tw.Write("(LosingInfo)");
                      //              tw.Flush();

                                }
                                else
                                {
                                    DecodeLastPacket(someData[dataIndex]);
                                    dataIndex++;
                                }

                                packetPosition = 0; // Reset to listen for new packet
                                valuesGrabbed++;
                            }
                        }
                    }
                    else
                    {
                        // Either a reset (new header) or loss of data
                        if (v != PACKET_MARKER)
                            packetPosition = NO_HEADER_SEEN;
                        else
                            packetPosition = FIRST_HEADER_SEEN; 
                     //   Warning("Data loss? " + lV + " " + v);
                     //   tw.Write("(DL?)");
                     //   tw.Flush();
                    }
//                    tw.Write("(SET_LV: " + v + ")");
//                    tw.Flush();
                    lV = v;
                    i++;
                }

                //tw.WriteLine();
            }
            //tw.Close();
            if (valuesGrabbed < someData.Length)
                return valuesGrabbed;
            else
                return someData.Length;
        }

        private int lastTimeStamp = 0;
        private int timeStamp = 0;
        private int diffMS = 0;
        private byte[] tempByte = new byte[1];

        /// <summary>
        /// Decode data that has been saved by MITesLogger (always send multiple of 4 bytes). A MITesLogger saves
        /// MITesData. This reads it back in so it behaves exactly as data read from the 
        /// serial port. Useful for "playing back" data that has been saved. 
        /// </summary>
        /// <param name="numPackets">The number of packets to read.</param>
        /// <param name="someData">The array in which the resulting MITesData will be stored.</param>
        /// <param name="dataIndex">The current index of the array in which the MITesData will be stored. (This will append data onto the end of existing data if needed).</param>
        /// <param name="br">A ByteReader object that has been opened to the proper file.</param>
        /// <returns>The new index for the someData array.</returns>
        public int DecodeMITesLoggerDataPLFormat(int numPackets, MITesData[] someData, int dataIndex, ByteReader br)
        {
            //Get new time to wait
            dTimeStamp = MITesLoggerReaderNew.ReadUnixTimeStamp(br);

            if (dTimeStamp == (double)MITesData.NONE)
            {
                Console.WriteLine("End of file.");
                return 0;
            }

            diffMS = (int)(dTimeStamp - dLastTimeStamp);
            if ((dLastTimeStamp != 0) && (dTimeStamp != 0))
                timeToWait = diffMS;
            else
                timeToWait = 0;

            // Wait the right number of MS if needed from last time data grabbed
            diffTime = Environment.TickCount - lastTimeStampTime;
            if ((timeToWait - diffTime) > 0)
            {
                Thread.Sleep(timeToWait - diffTime);
                timeToWait = 0;
            }

            dLastTimeStamp = dTimeStamp;
            lastTimeStampTime = Environment.TickCount;

            br.ReadByte(tempByte);
            packet[0] = tempByte[0];
            br.ReadByte(tempByte);
            packet[1] = tempByte[0];
            br.ReadByte(tempByte);
            packet[2] = tempByte[0];
            br.ReadByte(tempByte);
            packet[3] = tempByte[0];
            br.ReadByte(tempByte);
            packet[4] = tempByte[0];
            DecodeLastPacket(someData[dataIndex], false); // Don't swap bytes
            SetUnixTime(someData[dataIndex], dTimeStamp);// Set the time
            dataIndex++;
            return 1;
        }

        /// <summary>
        /// Decode data that has been saved by MITesLogger (always send multiple of 4 bytes). A MITesLogger saves
        /// MITesData. This reads it back in so it behaves exactly as data read from the 
        /// serial port. Useful for "playing back" data that has been saved. 
        /// </summary>
        /// <param name="numPackets">The number of packets to read.</param>
        /// <param name="someData">The array in which the resulting MITesData will be stored.</param>
        /// <param name="dataIndex">The current index of the array in which the MITesData will be stored. (This will append data onto the end of existing data if needed).</param>
        /// <param name="br">A ByteReader object that has been opened to the proper file.</param>
        /// <param name="isPLFormat">True if PLFormat, false if older version.</param>
        /// <returns>The new index for the someData array.</returns>
        public int DecodeMITesLoggerData(int numPackets, MITesData[] someData, int dataIndex, ByteReader br, bool isPLFormat)
        {
            if (isPLFormat)
                return DecodeMITesLoggerDataPLFormat(numPackets, someData, dataIndex, br);

            if (numPackets == 0)
                return DecodeMITesLoggerDataVariable(numPackets, someData, dataIndex, br);

            int valuesGrabbed = 0;
            for (int i = 0; i < numPackets; i++)
            {
                timeStamp = MITesLoggerReaderNew.ReadTimeStamp(br);
                //Console.WriteLine ("TIME: " + timeStamp);
                diffMS = timeStamp - lastTimeStamp;
                if ((lastTimeStamp != 0) && (timeStamp != 0))
                {
                    //Console.WriteLine ("Sleep: " + diffMS);
                    Thread.Sleep(diffMS);
                }
                lastTimeStamp = timeStamp;

                br.ReadByte(tempByte);
                packet[0] = tempByte[0];
                br.ReadByte(tempByte);
                packet[1] = tempByte[0];
                br.ReadByte(tempByte);
                packet[2] = tempByte[0];
                br.ReadByte(tempByte);
                packet[3] = tempByte[0];
                br.ReadByte(tempByte);
                packet[4] = tempByte[0];


                if (dataIndex >= someData.Length)
                    Warning("MAX_MITES_DATA too small! Losing info. Size:" + someData.Length);
                else
                {
                    DecodeLastPacket(someData[dataIndex], false); // Don't swap bytes
                    someData[dataIndex].timeStamp = timeStamp; // Set the time
                    dataIndex++;
                }
                valuesGrabbed++;
            }

            if (valuesGrabbed != numPackets)
                Console.WriteLine("ERROR: something wrong!!!");

            if (valuesGrabbed < someData.Length)
                return valuesGrabbed;
            else
                return someData.Length;
        }

        private int timeToWait = 0;
        private int lastTimeStampTime = Environment.TickCount;

        private bool isWaitTime = false;

        /// <summary>
        /// Decode data that has been saved by MITesLogger (always send multiple of 4 bytes). A MITesLogger saves
        /// MITesData. This reads it back in so it behaves exactly as data read from the 
        /// serial port. Useful for "playing back" data that has been saved. 
        /// </summary>
        /// <param name="numPackets">The number of packets to read.</param>
        /// <param name="someData">The array in which the resulting MITesData will be stored.</param>
        /// <param name="dataIndex">The current index of the array in which the MITesData will be stored. (This will append data onto the end of existing data if needed).</param>
        /// <param name="br">A ByteReader object that has been opened to the proper file.</param>
        /// <returns>The new index for the someData array.</returns>
        public int DecodeMITesLoggerDataVariable(int numPackets, MITesData[] someData, int dataIndex, ByteReader br)
        {
            if (isWaitTime)
                Console.WriteLine("Waiting: " + timeToWait);

            if (!isWaitTime)
            {
                //Get time to wait
                timeStamp = MITesLoggerReaderNew.ReadTimeStamp(br);

                if (timeStamp == MITesData.NONE)
                {
                    Console.WriteLine("End of file.");
                    return 0;
                }

                diffMS = timeStamp - lastTimeStamp;
                if ((lastTimeStamp != 0) && (timeStamp != 0))
                    timeToWait = diffMS;
                else
                    timeToWait = 0;
                lastTimeStamp = timeStamp;
                lastTimeStampTime = Environment.TickCount;
                isWaitTime = true;
                return 0;
            }
            else
            {
                if ((Environment.TickCount - lastTimeStampTime) >= timeToWait)
                {
                    br.ReadByte(tempByte);
                    packet[0] = tempByte[0];
                    br.ReadByte(tempByte);
                    packet[1] = tempByte[0];
                    br.ReadByte(tempByte);
                    packet[2] = tempByte[0];
                    br.ReadByte(tempByte);
                    packet[3] = tempByte[0];
                    br.ReadByte(tempByte);
                    packet[4] = tempByte[0];
                    DecodeLastPacket(someData[dataIndex], false); // Don't swap bytes
                    someData[dataIndex].timeStamp = timeStamp; // Set the time
                    dataIndex++;
                    isWaitTime = false;
                    return 1;
                }
                else
                    return 0;
            }
        }

        private double dTimeStamp = 0;
        private double dLastTimeStamp = 0;
        private int diffTime = 0;


        private int timeCount = 0;
        /// <summary>
        /// Decode data that has been saved by MITesLogger (always send multiple of 4 bytes). A MITesLogger saves
        /// MITesData. This reads it back in so it behaves exactly as data read from the 
        /// serial port. Useful for "playing back" data that has been saved. 
        /// </summary>
        /// <param name="numPackets">The number of packets to read.</param>
        /// <param name="someData">The array in which the resulting MITesData will be stored.</param>
        /// <param name="dataIndex">The current index of the array in which the MITesData will be stored. (This will append data onto the end of existing data if needed).</param>
        /// <param name="br">A ByteReader object that has been opened to the proper file.</param>
        /// <returns>The new index for the someData array.</returns>
        public int DecodeMITesLoggerDataOld(int numPackets, MITesData[] someData, int dataIndex, ByteReader br)
        {
            int valuesGrabbed = 0;
            for (int i = 0; i < numPackets; i++)
            {
                if (timeCount == 0)
                {
                    timeStamp = MITesLoggerReaderNew.ReadTimeStamp(br);
                    Console.WriteLine("TIME: " + timeStamp);
                }

                timeCount++;
                if (timeCount == MITesLoggerNew.TIMESTAMP_AFTER_SAMPLES)
                {
                    timeCount = 0;
                }

                br.ReadByte(tempByte);
                packet[0] = tempByte[0];
                br.ReadByte(tempByte);
                packet[1] = tempByte[0];
                br.ReadByte(tempByte);
                packet[2] = tempByte[0];
                br.ReadByte(tempByte);
                packet[3] = tempByte[0];
                br.ReadByte(tempByte);
                packet[4] = tempByte[0];
                br.ReadByte(tempByte);
                diffMS = (int)tempByte[0];

                Thread.Sleep(diffMS);
                timeStamp += diffMS; // MAYBE WORKS? SSI 

                if (dataIndex >= someData.Length)
                    Warning("MAX_MITES_DATA too small! Losing info. Size:" + someData.Length);
                else
                {
                    DecodeLastPacket(someData[dataIndex], false); // Don't swap bytes
                    someData[dataIndex].timeStamp = timeStamp; // Set the time
                    dataIndex++;
                }
                valuesGrabbed++;
            }

            if (valuesGrabbed != numPackets)
                Console.WriteLine("ERROR: something wrong!!!");

            if (valuesGrabbed < someData.Length)
                return valuesGrabbed;
            else
                return someData.Length;
        }
    }
}