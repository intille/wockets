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
        public byte _SensorID;

        /// <summary>
        /// The type of sensor based on the Types list
        /// </summary>
        public SensorDataType _Type;

        /// <summary>
        /// Set to true if this MITes data is an "alive" ping from a sensor, otherwise false.
        /// </summary>
        private bool isAlive;

        /// <summary>
        /// Set to true if this MITes data is a "battery low" message from a sensor, otherwise false.
        /// </summary>
        private bool isBatteryLow;

        public int _Length;

        public SensorData(byte numRawBytes,SensorDataType type, byte sensorID)
        {
            this._Length = numRawBytes;
            this.rawBytes = new byte[numRawBytes];
            this._Type = type;
            this._SensorID = sensorID;
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
            this._SensorID = 0;
            this._Type = 0;
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
