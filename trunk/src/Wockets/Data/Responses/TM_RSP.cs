using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Responses
{
    public class TM_RSP: Response
    {
        public TransmissionModes _TransmissionMode;
        public TM_RSP(int id):base(2,ResponseTypes.TM_RSP ,(byte)id)
        {
        }
    }
}
