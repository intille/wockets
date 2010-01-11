using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Receivers;
using Wockets.Decoders.Accelerometers;

namespace Wockets.Sensors.Accelerometers
{
    public sealed class Wocket: Accelerometer
    {

        private int config_time = 60;

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

        public bool Command()
        {
            RFCOMMReceiver rf= (RFCOMMReceiver)this._Receiver;
            this._Decoder.cmdMode = true;
            /*for(int i=0;i<3;i++)
            {
                rf.Send(Data.Commands.RFCOMMCommand.EnterCMD());
            }*/
            for (int i = 0; i < 100; i++)
            {
                if (!this._Decoder.cmdMode) return true;
                System.Threading.Thread.Sleep(50);
            }
            return false;

        }

        public int _Config_Timer
        {
            get
            {
                return this.config_time;
            }
            set
            {
                if (value < 30) this.config_time = 30;
                else if (value > 255) this.config_time = 255;
                else this.config_time = value;
                /*RFCOMMReceiver rf = ((RFCOMMReceiver)this._Receiver);
                rf.Send(Wockets.Data.Commands.RFCOMMCommand.SetCFT((short)this.config_time));
                rf.Send(Wockets.Data.Commands.RFCOMMCommand.SetCFT((short)this.config_time));
                rf.Send(Wockets.Data.Commands.RFCOMMCommand.Reset());
                 */
            }
        }

    }


}
