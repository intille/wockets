using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Types
{
    public class BatteryCalibration
    {
        public ushort _100Percentile;
        public ushort _80Percentile;
        public ushort _60Percentile;
        public ushort _40Percentile;
        public ushort _20Percentile;
        public ushort _10Percentile;
    }
}
