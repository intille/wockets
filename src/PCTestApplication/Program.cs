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

            string storage = @"C:\Users\albinali\Desktop\data\mites data\wockets\";
            WocketsController wc = new WocketsController("", "", "");
            wc.FromXML(storage+"SensorData.xml");
            int[] lostSeconds = new int[wc._Sensors.Count];
            double[] prevUnix = new double[wc._Sensors.Count];
            for (int i = 0; (i < wc._Sensors.Count); i++)
            {
                wc._Sensors[i]._RootStorageDirectory=storage+"data\\raw\\PLFormat\\";
                TextWriter tw = new StreamWriter(storage +"sensor" + wc._Sensors[i]._ID + ".csv");
                try
                {
                    int lastDecodedIndex = 0;
                    while (wc._Sensors[i].Load())
                    {
                        if (wc._Sensors[i]._Decoder._Head == 0)
                            lastDecodedIndex = wc._Sensors[i]._Decoder._Data.Length - 1;
                        else
                            lastDecodedIndex = wc._Sensors[i]._Decoder._Head - 1;

                        Wockets.Data.Accelerometers.AccelerationData data = (Wockets.Data.Accelerometers.AccelerationData)wc._Sensors[i]._Decoder._Data[lastDecodedIndex];            
                        tw.WriteLine(data.UnixTimeStamp + "," + data.X + "," + data.Y + "," + data.Z);

                        if ((prevUnix[i]>1000) &&((data.UnixTimeStamp-prevUnix[i])>60000))
                            lostSeconds[i]+=(int)((data.UnixTimeStamp-prevUnix[i])/1000.0);

                        prevUnix[i] = data.UnixTimeStamp;
                        
                    }
                }
                catch (Exception)
                {
                }
                tw.WriteLine("lost " + lostSeconds[i]);
                tw.Flush();
                tw.Close();
            }
        }
    }
}
