using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Data;

namespace Wockets.Data.Accelerometers
{
    public abstract class AccelerationData: SensorData
    {
        /// <summary>
        /// The x value of an accelerometer
        /// </summary>
        private short x;

        /// <summary>
        /// The y value of an accelerometer
        /// </summary>
        private short y;

        /// <summary>
        /// The z value of an accelerometer
        /// </summary>
        private short z;


        public AccelerationData(byte numRawBytes,byte sensorID)
            : base(numRawBytes, SensorDataType.ACCEL, sensorID)
        {
  
        }


        public void Reset()
        {
            base.Reset();
            this.x = 0;
            this.y = 0;
            this.z = 0;
        }

        public short X
        {
            get
            {
                return this.x;
            }
            set
            {
                this.x = value;
            }
        }

        public short Y
        {
            get
            {
                return this.y;
            }
            set
            {
                this.y = value;
            }
        }

        public short Z
        {
            get
            {
                return this.z;
            }
            set
            {
                this.z = value;
            }
        }

    }
}
