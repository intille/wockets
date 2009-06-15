using System;
using System.Collections.Generic;
using Wockets.Receivers;
using Wockets.Decoders.Accelerometers;

namespace Wockets.Sensors.Accelerometers
{
    public sealed class MITe: Accelerometer
    {

        public MITe():base(SensorClasses.MITes)
        {

        }
        /*
        public MITe(int id, string classname, string type, string location, string description)
            : base(id, SensorClasses.MITes, location, description)
        {
            this._Receiver = new StandardCOMReceiver();
            this._Decoder = new MITesDecoder();
        }
        */

        public override void Save()
        {
            base.Save();
        }

        public override void Load()
        {
            base.Load();
        }
        public override void Dispose()
        {
            base.Dispose();
        }
        public override string ToXML()
        {           
            return base.ToXML("");
        }
    }
}
