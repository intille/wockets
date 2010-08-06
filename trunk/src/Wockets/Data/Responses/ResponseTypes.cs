using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Responses
{
    public enum ResponseTypes: byte
    {
        BL_RSP=0,
        BP_RSP=1,
        PC_RSP=2,
        SENS_RSP=3,
        CAL_RSP=4,
        SR_RSP=5,
        ALT_RSP=6,
        PDT_RSP=7,
        TM_RSP=8,
        BTCAL_RSP=9,
        HV_RSP=10,
        FV_RSP=11,
        BC_RSP=12,
        AC_RSP=13
    }
}
