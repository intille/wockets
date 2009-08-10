using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public sealed class BatteryResponse : Responses.Response
    {
        private int batterylevel;

        public BatteryResponse(int id):base(3,SensorDataType.BATTERYLEVEL,(byte)id)
        {
        }

        public int BatteryLevel 
        {
            get
            {
                return this.batterylevel;
            }

            set
            {
                this.batterylevel = value;
            }
        }
    }
}
