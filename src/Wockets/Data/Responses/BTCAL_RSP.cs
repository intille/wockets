using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Responses
{
    public class BTCAL_RSP : Response
    {
        public int _CAL100;
        public int _CAL80;
        public int _CAL60;
        public int _CAL40;
        public int _CAL20;
        public int _CAL10;
        public BTCAL_RSP(int id)
            : base(10, ResponseTypes.BTCAL_RSP, (byte)id)
        {
        }
    }
}
