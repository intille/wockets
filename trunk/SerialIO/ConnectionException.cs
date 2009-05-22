using System;
using System.Collections.Generic;
using System.Text;

namespace HousenCS.SerialIO
{
    public class ConnectionException : Exception
    {

        public ConnectionException()
            : base()
        {
        }

        public ConnectionException(string message)
            : base(message)
        {

        }

    }
}
