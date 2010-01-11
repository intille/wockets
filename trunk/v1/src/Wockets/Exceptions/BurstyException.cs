using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Exceptions
{
    public class BurstyException: Exception
    {
        public BurstyException(string message): base(message)
        {
        }
    }
}
