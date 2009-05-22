using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Receivers;
using Wockets.Decoders.Accelerometers;

namespace Wockets.Sensors.Accelerometers
{
    public sealed class HTCDiamondTouch : Accelerometer
    {
        public HTCDiamondTouch():base(SensorClasses.HTCDiamondTouch)
        {

        }

        /*
        public HTCDiamondTouch(int id, string classname, string type, string location, string description)
            : base(id, SensorClasses.HTCDiamondTouch, location, description)
        {
            this._Receiver = new HTCDiamondReceiver();
            this._Decoder = new HTCDiamondTouchDecoder();
        }
        */

        public override string ToXML()
        {
            return base.ToXML("");
        }
    }
}
