using System;

namespace HousenCS.MITes
{
    /// <summary>
    /// Each type of MITesData has a unique Type ID. 
    /// </summary>
    public enum MITesTypes
    {
        /// <summary>
        /// Motion MITes go to sleep and wake up when moved, broadcasting the unique sensor ID. 
        /// </summary>
        STATIC,
        /// <summary>
        /// Temperature MITes transmit temperature about 1/s. 
        /// </summary>
        TEMP,
        /// <summary>
        /// Light MITes transmit a light level about 1/s. 
        /// </summary>
        LIGHT,
        /// <summary>
        /// UV MITes transmit a light level about 1/s. 
        /// </summary>
        UV,
        /// <summary>
        /// Current MITes transmit a current flow level about 1/s. 
        /// </summary>
        CURRENT,
        /// <summary>
        /// RFID MITes transmit an RFID tag ID when detected (usually from a wearable glove). 
        /// </summary>
        RFID,
        /// <summary>
        /// Humidity MITes transmit a humidty level about 1/s. 
        /// </summary>
        HUMIDITY,
        /// <summary>
        /// Distance MITes transmit value that represents an approximate maximum distance from  MITes. This can be
        /// used to roughly detect distance from a receiver. 
        /// </summary>
        DIST,
        /// <summary>
        /// 
        /// </summary>
        RANGE,
        /// <summary>
        /// HR MITes transmit a HR (from a wireless Polar band) about 1/s.
        /// </summary>
        HR,
        /// <summary>
        /// Reservered for future MITes expansion.
        /// </summary>
        RESERVED10,
        /// <summary>
        /// Reservered for future MITes expansion.
        /// </summary>
        IR,
        /// <summary>
        /// Reservered for future MITes expansion.
        /// </summary>
        RESERVED12,
        /// <summary>
        /// Reservered for future MITes expansion.
        /// </summary>
        RESERVED13,
        /// <summary>
        /// Reservered for future MITes expansion.
        /// </summary>
        RESERVED14,
        /// <summary>
        /// Reservered for future MITes expansion.
        /// </summary>
        RESERVED15,
        /// <summary>
        /// Mobile MITes accelerometer data. 
        /// </summary>
        ACCEL,
        /// <summary>
        /// Indicates that this raw data received is noise, because it has been filtered by 
        /// some MITes analyzer. If a MITesData object was created the data formed a legitimate
        /// packet.  
        /// </summary>
        NOISE
    }

    /// <summary>
    /// An object that stores a single MITes data packet of information as decoded. Also stores
    /// raw data. NOTE: It may be possible make code more efficient by changing this to a struct, 
    /// which is probably worth investigating (the problem is that some code depends upon 
    /// pass by reference not by value). 
    /// </summary>
    public class MITesData : IComparable
    {
        /// <summary>
        /// Representation of data with no value. Called by other classes. 
        /// </summary>
        public static readonly int NO_VALUE = -1;

        /// <summary>
        /// 
        /// </summary>
        public static readonly int NONE = -1;

        /// <summary>
        /// 
        /// </summary>
        public static readonly int EMPTY = 0;

        /// <summary>
        /// A packet always consists of 5 bytes. 
        /// </summary>
        public static readonly int MIN_NUM_RAW_BYTES = 5;

        public static readonly int MAX_NUM_RAW_BYTES = 6;

        /// <summary>
        /// The maximum number of MITes channels possible is 86 (due to FCC regulations, otherwise would be 256). In practice, chanels 
        /// between 0-20 are typically used, since lower channels get better performance.  
        /// </summary>
        public static readonly int MAX_MITES_CHANNELS = 86;

        /// <summary>
        /// The maximum number of steps of real resolution output by the mobile MITes. This 
        /// value is dependent on the resistor that is used.   
        /// </summary>
        //public static readonly int NUM_ACCEL_STEPS = 558;

        //for wockets and Built in Accelerometers
        public static readonly int NUM_ACCEL_STEPS = 1024;


        /// <summary>
        /// The channel number from which the data came from (typically 0 for all sensors other than accelerometers, and 1-68 for accelerometers).
        /// </summary>
        public byte channel;

        /// <summary>
        /// The type of sensor based on the Types list (see MITesData).
        /// </summary>
        public byte type;

        /// <summary>
        /// The resend ID of this data packet. Some sensors send the same data more than once in order to
        /// ensure the signal is received (e.g. motion MITes). The resend ID can be used to filter 
        /// repetitions. 
        /// </summary>
        public byte resendID;

        /// <summary>
        /// 
        /// </summary>
        public int fileID = 0;

        /// <summary>
        /// Set to true if this MITes data is an "alive" ping from a sensor, otherwise false.
        /// </summary>
        public bool isAlive;

        /// <summary>
        /// Set to true if this MITes data is a "battery low" message from a sensor, otherwise false.
        /// </summary>
        public bool isBatteryLow;

        /// <summary>
        /// The unique ID of the sensor. Accelerometers have no ID, all others do.   
        /// </summary>
        public short id;

        /// <summary>
        /// The x value of a mobile MITes accelerometer if MITesData is an accelerometer data point. Ranges from 0-800, usually (-10G to 10G).
        /// </summary>
        public short x;

        /// <summary>
        /// The y value of a mobile MITes accelerometer if MITesData is an accelerometer data point. Ranges from 0-800, usually (-10G to 10G).
        /// </summary>
        public short y;

        /// <summary>
        /// The z value of a mobile MITes accelerometer if MITesData is an accelerometer data point. Ranges from 0-800, usually (-10G to 10G).
        /// </summary>
        public short z;

        /// <summary>
        /// The int value of the sensor. How to interpret this value depends upon the sensor type. 
        /// </summary>
        public int sensorValue;

        /// <summary>
        /// The int value indicating how many recent activations there have been of the object motion sensor.
        /// This is only used for the object motion MITes. 
        /// </summary>
        public int recentActivationsValue;

        /// <summary>
        /// The system time at which this MITesData was decoded from the incoming raw data or data file.  
        /// </summary>
        public int timeStamp;

        /// <summary>
        /// The system UNIX time at which this MITesData was decoded from the incoming raw data or data file.  
        /// </summary>
        public double unixTimeStamp;

        /// <summary>
        /// A special character used as a sync character (when in repetition) in the raw MITes binary data. 
        /// </summary>
        public const byte MITes_SYNC_CHAR = 0x7E;

        /// <summary>
        /// The raw 5 byte packet that was used to decode this MITesData. This is saved so that raw data can be resaved
        /// in an efficient raw format later if desired. 
        /// </summary>
        public byte[] rawBytes;

        /// <summary>
        /// Constructor of an object to save valid, decoded data from a single MITes packet. 
        /// </summary>
        public MITesData()
        {
            rawBytes = new byte[MAX_NUM_RAW_BYTES];
            ResetVals();
        }

        private double ts;
        int IComparable.CompareTo(object obj)
        {
            ts = ((MITesData)obj).unixTimeStamp;
            if (this.unixTimeStamp < ts)
                return -1;
            else if (this.unixTimeStamp == ts)
                return 0;
            else
                return 1;
        }

        ///// <summary>
        ///// Copy the data from the argument MITes data object into the current object
        ///// </summary>
        ///// <param name="aMITesDataCopyFrom"></param>
        //public void CopyFrom(MITesData aMITesDataCopyFrom)
        //{
        //    this.channel = aMITesDataCopyFrom.channel;
        //    this.fileID = aMITesDataCopyFrom.fileID;
        //    this.id = aMITesDataCopyFrom.id;
        //    this.isAlive = aMITesDataCopyFrom.isAlive;
        //    this.isBatteryLow = aMITesDataCopyFrom.isBatteryLow;
        //    this.rawBytes = aMITesDataCopyFrom.rawBytes; // FIX
        //    this.recentActivationsValue = aMITesDataCopyFrom.recentActivationsValue;
        //    this.resendID = aMITesDataCopyFrom.resendID;
        //    this.sensorValue = aMITesDataCopyFrom.sensorValue;
        //    this.timeStamp = aMITesDataCopyFrom.timeStamp;
        //    this.ts = aMITesDataCopyFrom.ts;
        //    this.type = aMITesDataCopyFrom.type;
        //    this.unixTimeStamp = aMITesDataCopyFrom.unixTimeStamp;
        //    this.x = aMITesDataCopyFrom.x;
        //    this.y = aMITesDataCopyFrom.y;
        //    this.z = aMITesDataCopyFrom.z; 
        //}

        /// <summary>
        /// Return a String name for the MITesData type.
        /// </summary>
        /// <param name="typeNum">The type number (e.g. MITesTypes.HR)</param>
        /// <returns>A String name for the type (e.g. "Heart rate")</returns>
        public String GetStringOfType(int typeNum)
        {
            switch (typeNum)
            {
                case ((int)MITesTypes.STATIC):
                    return "Object motion";
                case ((int)MITesTypes.TEMP):
                    return "Temperature";
                case ((int)MITesTypes.LIGHT):
                    return "Light";
                case ((int)MITesTypes.HR):
                    return "Heart rate";
                case ((int)MITesTypes.UV):
                    return "Ultraviolet light";
                case ((int)MITesTypes.ACCEL):
                    return "Accelerometer";
                case ((int)MITesTypes.CURRENT):
                    return "Current flow";
                case ((int)MITesTypes.RFID):
                    return "RFID";
                case ((int)MITesTypes.DIST):
                    return "Distance";
                case ((int)MITesTypes.RESERVED10):
                    return "Reservered 10";
                case ((int)MITesTypes.IR):
                    return "IR";
                case ((int)MITesTypes.RESERVED12):
                    return "Reservered 12";
                case ((int)MITesTypes.RESERVED13):
                    return "Reservered 13";
                case ((int)MITesTypes.RESERVED14):
                    return "Reservered 14";
                case ((int)MITesTypes.RESERVED15):
                    return "Reservered 15";
                case ((int)MITesTypes.NOISE):
                    return "Noise";
            }
            return "UNKNOWN (Possible error)";
        }

        /// <summary>
        /// Create a readable string describing the MITesData. 
        /// </summary>
        /// <returns>A String that can be printed to Console and easily interpreted</returns>
        public override String ToString()
        {
            String str = "MITesData: " +
                "\nChan: " + channel + "\nID: " + id + "\nType: " + GetStringOfType(type) +
                "\nAlive: " + isAlive + "\nBat:" + isBatteryLow + "\nResend: " + resendID +
                "\nSensorVal:" + sensorValue +
                "\nRecentActivationsVal:" + recentActivationsValue +
                "\nX: " + x +
                "\nY: " + y +
                "\nZ: " + z +
                "\nIsNoise? " + (type == (int)MITesTypes.NOISE);
            return str;
        }

        /// <summary>
        /// 
        /// </summary>
        /// <returns></returns>
        public String ToCompactString()
        {
            String str = timeStamp + "," + unixTimeStamp + "," + channel + "," + x + "," + y + "," + z;
            return str;
        }


        /// <summary>
        /// Clear to zero the raw bytes for the object. 
        /// </summary>
        public void ResetRawVals()
        {
            for (int i = 0; i < MAX_NUM_RAW_BYTES; i++)
            {
                rawBytes[i] = (byte)0;
            }
        }

        /// <summary>
        /// Clear all the values in the MITesData object. 
        /// </summary>
        public void ResetVals()
        {
            channel = 0;
            id = 0;
            type = 0;
            isAlive = true;
            isBatteryLow = false;
            resendID = 0;
            sensorValue = 0;
            recentActivationsValue = 0;
            x = 0;
            y = 0;
            z = 0;
            timeStamp = NONE;
            //ResetRawVals();
        }
    }
}
