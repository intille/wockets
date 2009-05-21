using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Utils
{
    interface XMLSerializable
    {
        string ToXML();
        void FromXML(string xml);
    }
}
