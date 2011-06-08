using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class SET_LED: Command
    {
        public SET_LED(LEDTypes led,byte seconds)
        {
            this.cmd = new byte[] { (byte)0xa4, (byte)0 };
            switch (led)
            {
                case LEDTypes.Green:
                    cmd[1] = (byte)(0x1 << 6 | (seconds & 0x3f));
                    break;
                case LEDTypes.Yellow:
                    cmd[1] = (byte)(seconds & ((byte)0x3f));
                    break;
            }
            this.type = CommandTypes.SET_LED;
        }
    }
}
