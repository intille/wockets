using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Sensors
{
    /// <summary>
    /// An enumeration that defines the supported classes of sensors
    /// </summary>
    public enum SensorClasses : byte
    {

        /// <summary>
        /// MITes sensors
        /// </summary>
        MITes,
        /// <summary>
        /// Wockets sensors
        /// </summary>
        Wockets,
        /// <summary>
        /// HTC GSensors
        /// </summary>
        HTCDiamondTouch,
        /// <summary>
        /// Sparkfun sensors
        /// </summary>
        Sparkfun,

        /// <summary>
        /// Reserved for unknown classes
        /// </summary>
        Unknown
    }
}
