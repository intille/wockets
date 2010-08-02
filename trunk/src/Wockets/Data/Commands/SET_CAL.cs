using System;

using Wockets.Data.Types;

namespace Wockets.Data.Commands
{
    public class SET_CAL: Command
    {
        public SET_CAL(Calibration cal)
        {
            this._Bytes = new byte[] { (byte)0xa0 | (byte)CommandTypes.SET_CAL,
                (byte) (cal._X1G>>3),
                (byte) (((cal._X1G&0x07)<<4)|(cal._XN1G>>6)),
                (byte) (((cal._XN1G & 0x3f)<<1) |  (cal._Y1G>>9)),
                (byte) ((cal._Y1G>>2) & 0x7f),
                (byte) (((cal._Y1G&0x03)<<5)| (cal._Y1NG>>5)),
                (byte) (((cal._Y1NG&0x1f)<<2)| (cal._Z1G>>8)),
                (byte) ((cal._Z1G>>1)&0x7f),
                (byte) (((cal._Z1G&0x01)<<6)|(cal._Z1NG>>4)),
                (byte) ((cal._Z1NG&0x0f)<<3)};          
        }
    }
}
