using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Responses
{
    public class CAL_RSP: Response
    {
        public int _X1G;
        public int _XN1G;
        public int _Y1G;
        public int _YN1G;
        public int _Z1G;
        public int _ZN1G;
        public CAL_RSP(int id):base(10,ResponseTypes.CAL_RSP,(byte)id)
        {
        }
    }
}
