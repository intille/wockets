using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Receivers;
using Wockets.Decoders.Accelerometers;

namespace Wockets.Sensors.Accelerometers
{
    public sealed class HTCDiamondTouch : Accelerometer
    {
        /// <summary>
        /// A constructor that instatnitates an HTC internal GSensor accelerometer
        /// </summary>
        public HTCDiamondTouch():base(SensorClasses.HTCDiamondTouch)
        {

        }

        /// <summary>
        /// A method that saves the accelerometer data
        /// </summary>
        public override void Save()
        {
            base.Save();
        }

        /// <summary>
        /// A method that loads the accelerometer data one packet at a time
        /// </summary>
        /// <returns></returns>
        public override bool Load()
        {
            return base.Load();
        }

        /// <summary>
        /// A method that releases the resources associated with the accelerometer
        /// </summary>
        public override void Dispose()
        {
            base.Dispose();
        }

        /// <summary>
        /// A method that serializes the HTC internal accerometer into an XML string
        /// </summary>
        /// <returns>An xml string that describes the accelerometr</returns>
        public override string ToXML()
        {
            return base.ToXML("");
        }
    }
}
