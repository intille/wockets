using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Utils.Tapi;

namespace Wockets
{
    public static class CurrentPhone
    {
        public static string _IMEI = "";
        public static string _Number = "";

        static CurrentPhone()
        {
         
            //Get the phone's IMEI
            try
            {
                Tapi t = new Tapi();
                t.Initialize();
                Line _line = t.CreateLine(0, LINEMEDIAMODE.INTERACTIVEVOICE, LINECALLPRIVILEGE.MONITOR);

                            int address=0;

                if (CellTSP.lineGetCurrentAddressID(_line.hLine,out address) != 0)
                {
                    throw new System.ComponentModel.Win32Exception(System.Runtime.InteropServices.Marshal.GetLastWin32Error(), "TAPI Error: " + System.Runtime.InteropServices.Marshal.GetLastWin32Error().ToString("X"));
                }

                byte[] buffer = new byte[512];
                //write size
                BitConverter.GetBytes(512).CopyTo(buffer, 0);

                if (CellTSP.lineGetGeneralInfo(_line.hLine, buffer) != 0)
                {
                    throw new System.ComponentModel.Win32Exception(System.Runtime.InteropServices.Marshal.GetLastWin32Error(), "TAPI Error: " + System.Runtime.InteropServices.Marshal.GetLastWin32Error().ToString("X"));
                }

                int serialsize = BitConverter.ToInt32(buffer, 36);
                int serialoffset = BitConverter.ToInt32(buffer, 40);
                _IMEI = System.Text.Encoding.Unicode.GetString(buffer, serialoffset, serialsize);
                _IMEI = _IMEI.Substring(0, _IMEI.IndexOf(Convert.ToChar(0)));
                
            }
            catch (Exception e)
            {
            }

            //Get the phone's number

            //Get the phone's IMEI
            try
            {
                Tapi t = new Tapi();
                t.Initialize();
                Line _line = t.CreateLine(0, LINEMEDIAMODE.INTERACTIVEVOICE, LINECALLPRIVILEGE.MONITOR);

    

            }
            catch (Exception e)
            {
            }
        }
    }
}
