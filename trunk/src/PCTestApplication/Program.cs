using System;
using System.Collections.Generic;
using System.Text;
using System.IO;
using Wockets;

namespace PCTestApplication
{
    class Program
    {
        static void Main(string[] args)
        {
            string storage=@"C:\SampleFile\";
            WocketsController wc = new WocketsController("", "", "");
            wc.FromXML(storage+"SensorData.xml");
            for (int i = 0; (i < wc._Sensors.Count); i++)
            {
                wc._Sensors[i]._RootStorageDirectory=storage+"data\\raw\\PLFormat\\";
                TextWriter tw = new StreamWriter(storage +"sensor" + wc._Sensors[i]._ID + ".csv");
                try
                {
                    while (wc._Sensors[i].Load())
                    {
                        Wockets.Data.Accelerometers.AccelerationData data = (Wockets.Data.Accelerometers.AccelerationData)wc._Sensors[i]._Decoder._Data[0];
                        tw.WriteLine(data.UnixTimeStamp + "," + data.X + "," + data.Y + "," + data.Z);
                    }
                }
                catch (Exception)
                {
                }
                tw.Flush();
                tw.Close();
            }
        }
    }
}
