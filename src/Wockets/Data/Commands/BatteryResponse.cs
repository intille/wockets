using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public sealed class BatteryResponse : SensorData
    {
        private int batterylevel;

        public BatteryResponse():base(3,SensorDataType.BATTERYLEVEL,(byte)0)
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
