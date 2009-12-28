using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Decoders
{

    public class Response
    {
        public class ResponseArgs : EventArgs
        {
            private Wockets.Data.SensorData response;


            public Wockets.Data.SensorData _Response
            {
                get
                {
                    return this.response;
                }

                set
                {
                    this.response = value;
                }
            }

        }

        public delegate void ResponseHandler(object sender, ResponseArgs e);

    }

}
