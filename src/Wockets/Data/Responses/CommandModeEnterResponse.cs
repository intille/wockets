using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Responses
{
    public sealed class CommandModeEnterResponse: Response
    {


        public CommandModeEnterResponse(int id):base(0,SensorDataType.COMMAND_MODE_ENTERED,(byte)id)
        {
        }

    }
}
