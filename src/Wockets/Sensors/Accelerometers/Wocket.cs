using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Receivers;
using Wockets.Decoders.Accelerometers;

namespace Wockets.Sensors.Accelerometers
{
    public sealed class Wocket: Accelerometer
    {

        /// <summary>
        /// A constructor that instantiates a wocket accelerometer
        /// </summary>
        public Wocket():base(SensorClasses.Wockets)
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
        /// A method that loads accelerometer data once at a time
        /// </summary>
        /// <returns>True if a data packet is successfully loaded, otherwise false</returns>
        public override bool Load()
        {
            return base.Load();
        }

        /// <summary>
        /// A method that dispose and releases the resources associated with the accelerometer object
        /// </summary>
        public override void Dispose()
        {
            base.Dispose();
        }


        /// <summary>
        /// A method that serializes the accelerometer into an XML string
        /// </summary>
        /// <returns>A serialized XML string that describes a wocket accelerometer</returns>
        public override string ToXML()
        {
            return base.ToXML("");
        }

    }


}
