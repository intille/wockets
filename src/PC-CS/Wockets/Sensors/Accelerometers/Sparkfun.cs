using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Receivers;
using Wockets.Decoders.Accelerometers;

namespace Wockets.Sensors.Accelerometers
{
    public sealed class Sparkfun: Accelerometer
    {
        public Sparkfun():base(SensorClasses.Sparkfun)
        {

        }

        /*
        public Sparkfun(int id, string classname, string location, string description)
            : base(id, SensorClasses.Sparkfun, location, description)
        {
            this._Receiver = new RFCOMMReceiver();
            this._Decoder = new SparkfunDecoder();
        }*/

        public override void Save()
        {
            base.Save();
        }

        public override bool Load()
        {
            return base.Load();
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
