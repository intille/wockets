using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Receivers
{
    class GenericReceiver : Receiver
    {

        public GenericReceiver()
            : base(1)
        {
        }

        public override bool Initialize()
        {
            return false;
        }

        public override bool Dispose()
        {
            return false;
        }

        public override void Update()
        {

        }
        public override string ToXML()
        {
            return "Error";
        }

        public override void FromXML(string xml)
        {

        }



        public override int CompareTo(object o)
        {
            return 0;
        }


    }
}
