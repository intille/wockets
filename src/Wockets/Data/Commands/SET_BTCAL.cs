using System;
using Wockets.Data.Types;

namespace Wockets.Data.Commands
{
    public class SET_BTCAL: Command
    {

        public SET_BTCAL(BatteryCalibration cal)
        {
            this._Bytes = new byte[] { (byte)0xa0 | (byte)CommandTypes.SET_BTCAL,
                (byte) (cal._100Percentile>>3),
                (byte) (((cal._100Percentile&0x07)<<4)|(cal._80Percentile>>6)),
                (byte) (((cal._80Percentile & 0x3f)<<1) |  (cal._60Percentile>>9)),
                (byte) ((cal._60Percentile>>2) & 0x7f),
                (byte) (((cal._60Percentile&0x03)<<5)| (cal._40Percentile>>5)),
                (byte) (((cal._40Percentile&0x1f)<<2)| (cal._20Percentile>>8)),
                (byte) ((cal._20Percentile>>1)&0x7f),
                (byte) (((cal._20Percentile&0x01)<<6)|(cal._10Percentile>>4)),
                (byte) ((cal._10Percentile&0x0f)<<3)};
        }
    }
}
