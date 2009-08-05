using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Commands
{
    public class RFCOMMCommand : ReceiverCommand
    {
        private static byte[][] commands = new byte[][] { 
            new byte[] { (byte)36, (byte)36, (byte)36 },
            new byte[] { (byte)'-', (byte)'-', (byte)'-', (byte)13 }, 
            new byte[] { (byte)'R', (byte)',', (byte)'1' },
            new byte[] { (byte)0xa0 }, 
            new byte[] { (byte)0xa1 }, 
            new byte[] { (byte)'G', (byte)'W', (byte)13 },
            new byte[] { (byte)'S', (byte)'W', (byte)',', (byte)'0', (byte)'0', (byte)'0', (byte)'0', (byte)13 }, 
            new byte[] { (byte)0xa4, (byte)0},
            new byte[] { (byte)0xa6 }, 
            new byte[] { (byte)0xa7, (byte)0 }, 
            new byte[] { (byte)0xa8 }, 
            new byte[] { (byte)0xa9, (byte)0, (byte)0, (byte)0, (byte)0, (byte)0, (byte)0, (byte)0, (byte)0, (byte)0 }, 
            new byte[] { (byte)'G', (byte)'Y', (byte)13 }, 
            new byte[] { (byte)'S', (byte)'Y', (byte)',', (byte)0, (byte)0, (byte)0, (byte)0, (byte)13 }, 
            new byte[] { (byte) 0xac }, 
            new byte[] { (byte)0xad, (byte)0 }, 
            new byte[] { (byte)'G', (byte)'I', (byte)13 }, 
            new byte[] { (byte)'S', (byte)'I', (byte)',', (byte)0, (byte)0, (byte)0, (byte)0, (byte)13 }, 
            new byte[] { (byte)'G', (byte)'Q', (byte)13 },
            new byte[] {}, 
            new byte[] { (byte)0xb2 }, 
            new byte[] { (byte)0xb3, (byte)0 }, 
            new byte[] { (byte)0xb4 }, 
            new byte[] { (byte)0xb5, (byte)0 }, 
            new byte[] { (byte)0xb6 }, 
            new byte[] { (byte)'G', (byte)'T', (byte)13}, 
            new byte[] {}, 
            new byte[] { (byte)0xb9 },
            new byte[] { (byte)0xbb }};

        private static CommandTypes[] cmd_types ={
            CommandTypes.ENTER_CMD_MODE,
            CommandTypes.EXIT_CMD_MODE, 
            CommandTypes.RESET, 
            CommandTypes.GET_BATTERY, 
            CommandTypes.GET_PC, 
            CommandTypes.GET_SNIFF_MODE, 
            CommandTypes.SET_SNIFF_MODE, 
            CommandTypes.SET_LED, 
            CommandTypes.GET_SENSITIVITY, 
            CommandTypes.SET_SENSITIVITY, 
            CommandTypes.GET_CALIBRATION, 
            CommandTypes.SET_CALIBRATION, 
            CommandTypes.GET_TRANSMISSION_POWER, 
            CommandTypes.SET_TRANSMISSION_POWER, 
            CommandTypes.GET_SAMPLING_RATE, 
            CommandTypes.SET_SAMPLING_RATE,
            CommandTypes.GET_DSC,
            CommandTypes.SET_DSC,
            CommandTypes.GET_TRANSMISSION_MODE, 
            CommandTypes.SET_TRANSMISSION_MODE, 
            CommandTypes.GET_ALIVE_TIME, 
            CommandTypes.SET_ALIVE_TIME, 
            CommandTypes.GET_POWERDOWN_TIME, 
            CommandTypes.SET_POWERDOWN_TIME, 
            CommandTypes.RESET_WOCKET, 
            CommandTypes.GET_CONFIGURATION_TIME, 
            CommandTypes.SET_CONFIGURATION_TIME, 
            CommandTypes.GET_BAUD_RATE, 
            CommandTypes.SET_BAUD_RATE,
            CommandTypes.ALIVE};

        private RFCOMMCommand(int i)
        {
            this.cmd = commands[i];
            this.type = cmd_types[i];
        }

        private RFCOMMCommand(byte[]_cmd,CommandTypes _type)
        {
            this.cmd=_cmd;
            this.type=_type;
        }

        public static RFCOMMCommand EnterCMD()
        {
            return new RFCOMMCommand(0);
        }

        public static RFCOMMCommand ExitCMD()
        {
            return new RFCOMMCommand(1);
        }

        public static RFCOMMCommand Reset()
        {
            return new RFCOMMCommand(2);
        }

        public static RFCOMMCommand GetBT()
        {
            return new RFCOMMCommand(3);
        }

        public static RFCOMMCommand GetPC()
        {
            return new RFCOMMCommand(4);
        }

        public static RFCOMMCommand GetSM()
        {
            return new RFCOMMCommand(5);
        }

        public static RFCOMMCommand SetSM(short i)
        {
            byte[] bytes;
            bytes = BitConverter.GetBytes(i);
            char[] chs= String.Format("{0}{1}",
                padString(bytes[0].ToString("X")),
                padString(bytes[1].ToString("X"))).ToCharArray();
            bytes=commands[6];
            bytes[3] = (byte)chs[0];
            bytes[4] = (byte)chs[1];
            bytes[5] = (byte)chs[2];
            bytes[6] = (byte)chs[4];
            return new RFCOMMCommand(bytes,CommandTypes.SET_SNIFF_MODE);
        }

        public static RFCOMMCommand SetLED(LED color, short time)
        {
            byte[] cmd = commands[7];
            switch (color)
            {
                case LED.GREEN:
                    cmd[1] = (byte)(0x1 << 6 + time);
                    break;
                case LED.YELLOW:
                    cmd[1] = (byte)time;
                    break;
            }
            return new RFCOMMCommand(cmd, cmd_types[7]);
        }

        public static RFCOMMCommand GetSEN()
        {
            return new RFCOMMCommand(8);
        }

        public static RFCOMMCommand SetSEN(Sensitivity sens)
        {
            byte[] cmd = commands[9];
            switch (sens)
            {
                case Sensitivity.LOW:
                    break;
                case Sensitivity.MID_LOW:
                    cmd[1] = (byte)(0x1 << 4);
                    break;
                case Sensitivity.MID_HIGH:
                    cmd[1] = (byte)(0x2 << 4);
                    break;
                case Sensitivity.HIGH:
                    cmd[1] = (byte)(0x3 << 4);
                    break;
            }
            return new RFCOMMCommand(cmd, cmd_types[9]);
        }

        public static RFCOMMCommand GetCAL()
        {
            return new RFCOMMCommand(10);
        }

        public static RFCOMMCommand SetCAL(short x, short xn, short y, short yn, short z, short zn)
        {
            byte[] cmd = commands[11];
            cmd[1] = (byte)(0x7f & x >> 3);
            cmd[2] = (byte)((0x70 & x << 4) | (0x0f & xn >> 6));
            cmd[3] = (byte)((0x7e & xn << 1) | (0x01 & y >> 9));
            cmd[4] = (byte)(0x7f & y >> 2);
            cmd[5] = (byte)((0x60 & y << 5) | (0x1f & yn >> 5));
            cmd[6] = (byte)((0x7c & yn << 2) | (0x03 & z >> 8));
            cmd[7] = (byte)(0x7f & z >> 1);
            cmd[8] = (byte)((0x40 & z << 6) | (0x3f & zn >> 4));
            cmd[9] = (byte)(0x78 & zn << 3);
            return new RFCOMMCommand(cmd, cmd_types[11]);
        }

        public static RFCOMMCommand GetTP()
        {
            return new RFCOMMCommand(12);
        }

        public static RFCOMMCommand SetTP(Transmission_Strength strength)
        {
            byte[] cmd = commands[13];
            switch (strength)
            {
                case Transmission_Strength.VERY_WEAK:
                    cmd[3] = (byte)'F';
                    cmd[4] = (byte)'F';
                    cmd[5] = (byte)'E';
                    cmd[6] = (byte)'8';
                    break;
                case Transmission_Strength.WEAK:
                    cmd[3] = (byte)'F';
                    cmd[4] = (byte)'F';
                    cmd[5] = (byte)'F';
                    cmd[6] = (byte)'0';
                    break;
                case Transmission_Strength.MEDIUM_WEAK:
                    cmd[3] = (byte)'F';
                    cmd[4] = (byte)'F';
                    cmd[5] = (byte)'F';
                    cmd[6] = (byte)'4';
                    break;
                case Transmission_Strength.MEDIUM:
                    cmd[3] = (byte)'F';
                    cmd[4] = (byte)'F';
                    cmd[5] = (byte)'F';
                    cmd[6] = (byte)'8';
                    break;
                case Transmission_Strength.MEDIUM_STR0NG:
                    cmd[3] = (byte)'F';
                    cmd[4] = (byte)'F';
                    cmd[5] = (byte)'F';
                    cmd[6] = (byte)'C';
                    break;
                case Transmission_Strength.STRONG:
                    cmd[3] = (byte)'0';
                    cmd[4] = (byte)'0';
                    cmd[5] = (byte)'0';
                    cmd[6] = (byte)'1';
                    break;
                case Transmission_Strength.VERY_STRONG:
                    cmd[3] = (byte)'0';
                    cmd[4] = (byte)'0';
                    cmd[5] = (byte)'0';
                    cmd[6] = (byte)'4';
                    break;
            }
            return new RFCOMMCommand(cmd, cmd_types[13]);
        }

        public static RFCOMMCommand GetSR()
        {
            return new RFCOMMCommand(14);
        }

        public static RFCOMMCommand SetSR(short rate)
        {
            byte[] cmd = commands[15];
            cmd[1] = (byte)(0x7f & rate);
            return new RFCOMMCommand(cmd,cmd_types[15]);
        }

        public static RFCOMMCommand GetDSC()
        {
            return new RFCOMMCommand(16);
        }

        public static RFCOMMCommand SetDSC(short i)
        {
            byte[] bytes;
            bytes = BitConverter.GetBytes(i);
            char[] chs = String.Format("{0}{1}",
                padString(bytes[0].ToString("X")),
                padString(bytes[1].ToString("X"))).ToCharArray();
            bytes = commands[17];
            bytes[3] = (byte)chs[0];
            bytes[4] = (byte)chs[1];
            bytes[5] = (byte)chs[2];
            bytes[6] = (byte)chs[4];
            return new RFCOMMCommand(bytes, CommandTypes.SET_DSC);
        }

        public static RFCOMMCommand GetTM()
        {
            return new RFCOMMCommand(18);
        }

        public static RFCOMMCommand SetTM(Transmission_Mode mode)
        {
            byte[] cmd;
            switch (mode)
            {
                case Transmission_Mode.LATENCY:
                    cmd = new byte[] { (byte)'S', (byte)'Q', (byte)',', (byte)'1', (byte)'6', (byte)13 };
                    return new RFCOMMCommand(cmd, cmd_types[19]);
                case Transmission_Mode.THROUGHPUT:
                    cmd = new byte[] { (byte)'S', (byte)'Q', (byte)',', (byte)'0', (byte)13 };
                    return new RFCOMMCommand(cmd, cmd_types[19]);
            }
            return null;
        }

        public static RFCOMMCommand GetALT()
        {
            return new RFCOMMCommand(20);
        }

        public static RFCOMMCommand SetALT(short i)
        {
            byte[] cmd = commands[21];
            cmd[1] = (byte)(0x7f & i);
            return new RFCOMMCommand(cmd, cmd_types[21]);
        }

        public static RFCOMMCommand GetPDT()
        {
            return new RFCOMMCommand(22);
        }

        public static RFCOMMCommand SetPDT(short i)
        {
            byte[] cmd = commands[23];
            cmd[1] = (byte)(0x7f & i);
            return new RFCOMMCommand(cmd, cmd_types[23]);
        }

        public static RFCOMMCommand ResetWK()
        {
            return new RFCOMMCommand(24);
        }

        public static RFCOMMCommand GetCFT()
        {
            return new RFCOMMCommand(25);
        }

        public static RFCOMMCommand SetCFT(short time)
        {
            char[] chs = time.ToString().ToCharArray();
            byte[] bytes = new byte[3 + chs.Length];
            bytes[0] = (byte)'S';
            bytes[1] = (byte)'T';
            bytes[2] = (byte)',';
            for (int i = 0; i < chs.Length; i++)
            {
                bytes[i+3] = (byte)chs[i];
            }
            return new RFCOMMCommand(bytes,cmd_types[26]);
        }

        public static RFCOMMCommand GetBR()
        {
            return new RFCOMMCommand(27);
        }

        public static RFCOMMCommand Alive()
        {
            return new RFCOMMCommand(28);
        }


        public enum LED
        {
            YELLOW,
            GREEN
        }

        public enum Sensitivity
        {
            LOW,
            MID_LOW,
            MID_HIGH,
            HIGH
        }

        public enum Transmission_Strength
        {
            VERY_WEAK,
            WEAK,
            MEDIUM_WEAK,
            MEDIUM,
            MEDIUM_STR0NG,
            STRONG,
            VERY_STRONG
        }

        public enum Transmission_Mode
        {
            LATENCY,
            THROUGHPUT
        }

        private static string padString(string s)
        {
            while (s.Length < 2) s = "0" + s;
            return s;
        }
		
    }
}
