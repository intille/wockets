using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Receivers;
using Wockets.Decoders.Accelerometers;

namespace Wockets.Sensors.Accelerometers
{
    public sealed class Wocket: Accelerometer
    {
        public Wocket():base(SensorClasses.Wockets)
        {
        }

        /*
        public Wocket(int id, string classname, string type, string location, string description)
            : base(id, SensorClasses.Wockets, location, description)
        {
            this._Receiver = new RFCOMMReceiver();
            this._Decoder = new WocketsDecoder();
        }
        */

        public override string ToXML()
        {
            return base.ToXML("");
        }
    }


}
