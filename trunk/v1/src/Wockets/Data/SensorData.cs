using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data
{
    public abstract class SensorData: IComparable
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
        /// Packet size
        /// </summary>
        private byte numRawBytes;

        /// <summary>
        /// The system UNIX time at which this MITesData was decoded from the incoming raw data or data file.  
        /// </summary>
        private double unixTimeStamp;

        private double ts;

        /// <summary>
        /// The raw byte packet
        /// </summary>
        private byte[] rawBytes;

        /// <summary>
        /// The channel number from which the data came from
        /// </summary>
        private byte sensorID;

        /// <summary>
        /// The type of sensor based on the Types list
        /// </summary>
        private SensorDataType type;

        /// <summary>
        /// Set to true if this MITes data is an "alive" ping from a sensor, otherwise false.
        /// </summary>
        private bool isAlive;

        /// <summary>
        /// Set to true if this MITes data is a "battery low" message from a sensor, otherwise false.
        /// </summary>
        private bool isBatteryLow;


        public SensorData(byte numRawBytes,SensorDataType type, byte sensorID)
        {
            this.numRawBytes = numRawBytes;
            this.rawBytes = new byte[numRawBytes];
            this.type = type;
            this.sensorID = sensorID;
        }

        public bool IsAlive
        {
            get
            {
                return this.isAlive;
            }

            set
            {
                this.isAlive = value;
            }
        }

        public bool IsBatteryLow
        {
            get
            {
                return this.isBatteryLow;
            }
            set
            {
                this.isBatteryLow = value;
            }
        }
        public byte SensorID
        {
            get
            {
                return this.sensorID;
            }

            set
            {
                this.sensorID = value;
            }
        }

        public SensorDataType Type
        {
            get
            {
                return this.type;
            }

            set
            {
                this.type = value;
            }
        }
        public double UnixTimeStamp
        {
            get
            {
                return this.unixTimeStamp;
            }
            set
            {
                this.unixTimeStamp = value;
            }
        }
        public byte NumRawBytes
        {
            get
            {
                return this.numRawBytes;
            }
            set
            {
                this.numRawBytes = value;
            }
        }

        public byte[] RawBytes
        {
            get
            {
                return this.rawBytes;
            }
            set
            {
                this.rawBytes = value;
            }
        }

        protected void Reset()
        {
            this.sensorID = 0;
            this.type = 0;
            this.isAlive = true;
            this.isBatteryLow = false;
            for (int i = 0; i < this.numRawBytes; i++)
            {
                this.rawBytes[i] = (byte)0;
            }
        }

        int IComparable.CompareTo(object obj)
        {
            ts = ((SensorData)obj).unixTimeStamp;
            if (this.unixTimeStamp < ts)
                return -1;
            else if (this.unixTimeStamp == ts)
                return 0;
            else
                return 1;
        }
    }
}
