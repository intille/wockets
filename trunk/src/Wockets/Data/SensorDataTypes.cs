using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data
{
    public enum SensorDataType : byte
    {
               
        /// <summary>
        /// Motion Sensor go to sleep and wake up when moved, broadcasting the unique sensor ID. 
        /// </summary>
        STATIC,
        /// <summary>
        /// Temperature Sensor transmit temperature about 1/s. 
        /// </summary>
        TEMP,
        /// <summary>
        /// Light Sensor transmit a light level about 1/s. 
        /// </summary>
        LIGHT,
        /// <summary>
        /// UV Sensor transmit a light level about 1/s. 
        /// </summary>
        UV,
        /// <summary>
        /// Current Sensor transmit a current flow level about 1/s. 
        /// </summary>
        CURRENT,
        /// <summary>
        /// RFID Sensor transmit an RFID tag ID when detected (usually from a wearable glove). 
        /// </summary>
        RFID,
        /// <summary>
        /// Humidity Sensor transmit a humidty level about 1/s. 
        /// </summary>
        HUMIDITY,
        /// <summary>
        /// Distance Sensor transmit value that represents an approximate maximum distance from  Sensor. This can be
        /// used to roughly detect distance from a receiver. 
        /// </summary>
        DIST,
        /// <summary>
        /// 
        /// </summary>
        RANGE,
        /// <summary>
        /// HR Sensor transmit a HR (from a wireless Polar band) about 1/s.
        /// </summary>
        HR,
        /// <summary>
        /// Reservered for future Sensor expansion.
        /// </summary>
        RESERVED10,
        /// <summary>
        /// Reservered for future Sensor expansion.
        /// </summary>
        IR,
        /// <summary>
        /// Reservered for future Sensor expansion.
        /// </summary>
        RESERVED12,
        /// <summary>
        /// Reservered for future Sensor expansion.
        /// </summary>
        RESERVED13,
        /// <summary>
        /// Reservered for future Sensor expansion.
        /// </summary>
        RESERVED14,
        /// <summary>
        /// Reservered for future Sensor expansion.
        /// </summary>
        RESERVED15,

        BATTERYLEVEL,
        /// <summary>
        /// Mobile Sensor accelerometer data. 
        /// </summary>
        ACCEL,
        /// <summary>
        /// Indicates that this raw data received is noise  
        /// </summary>
        NOISE
    }
}
