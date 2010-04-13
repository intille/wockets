using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Responses
{
    public class BaudRateResponse: Response
    {
         public string _BaudRate;

        public BaudRateResponse(int id):base(3,SensorDataType.BAUD_RATE,(byte)id)
        {
        }

    }
}
