using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Data.Types;

namespace Wockets.Data.Responses
{
    public class SENS_RSP: Response
    {
        public Sensitivity _Sensitivity;

        public SENS_RSP(int id)
            : base(2, ResponseTypes.SENS_RSP, (byte)id)
        {
        }
    }
}
