using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Data.Types;

namespace Wockets.Data.Responses
{
    public class TM_RSP: Response
    {
        public TransmissionMode _TransmissionMode;
        public TM_RSP(int id):base(2,ResponseTypes.TM_RSP ,(byte)id)
        {
        }
    }
}
