using System;
using System.Collections.Generic;
using System.Text;
using BluetoothLayer;
using System.IO.Ports;
using System.Threading;
using System.IO;

namespace BluetoothLayerTest
{
    class Program
    {

        static void main2()
        {
            byte[] buffer = new byte[100];
            BluetoothLayer.BluetoothLayer bt = new BluetoothLayer.BluetoothLayer();
            byte[] addr = { 0x00, 0xa0, 0x96, 0x26, 0xd8, 0x97 };
            string comPortName = bt.prepareCOMport(addr, "0000");
            comPortName = "COM6:";
            SerialPort port = new SerialPort(comPortName);
            port.BaudRate = 9600;
            port.StopBits = StopBits.One;
            port.DataBits = 8;
            port.Parity = Parity.None;
            //port.ReadTimeout = 999999999;


            port.Open();
            //port.Write("testing\r\n");
            port.Read(buffer, 0, buffer.Length);
            port.Close();
        }

        static void main3()
        {
            BluetoothStream stream = BluetoothStream.OpenConnection(new byte[] { 0x00, 0x14, 0xc5, 0xa1, 0x01, 0xad }, "1111");//0x00, 0x06, 0x66, 0x00, 0xd6, 0xdf }, "1111");
            byte[] buffer = new byte[1024];
            FileInfo info = new FileInfo("output.txt");
            FileStream outStream = info.Open(FileMode.Create, FileAccess.ReadWrite, FileShare.None);
            BinaryWriter writer = new BinaryWriter(outStream);

            bool thebool = true;
            while (thebool)
            {
                if (stream == null)
                {
                    try
                    {
                        stream = BluetoothStream.OpenConnection(new byte[] { 0x00, 0x14, 0xc5, 0xa1, 0x01, 0xad }, "1111");//0x00, 0x06, 0x66, 0x00, 0xd6, 0xdf }, "1111");
                    }
                    catch
                    {
                        stream = null;
                        continue;
                    }
                }
                try
                {
                    int bytesRead = stream.Read(buffer, 0, buffer.Length);
                    writer.Write(DateTime.Now.ToString() + ": " + bytesRead);
                    writer.Flush();
                }
                catch (Exception e)
                {
                    stream = null;
                }
            }
            writer.Close();
            outStream.Close();
            stream.Close();
        }

        static void Main(string[] args)
        {
            main3();
            return;

            FileInfo info = new FileInfo("output.bin");
            FileStream outStream = info.Open(FileMode.Create, FileAccess.ReadWrite, FileShare.None);

            byte[] buffer = new byte[100];
            BluetoothLayer.BluetoothLayer bt = new BluetoothLayer.BluetoothLayer();
            byte[] addr = {0x00, 0x06, 0x66, 0x00, 0xd7, 0x58};
            string comPortName = bt.prepareCOMport(addr, "1234");
            SerialPort port = new SerialPort(comPortName);
            port.BaudRate = 57600;

            int closes = 0;
            int totalRead = 0;
            int retries = 0;
            for (int ii = 0; ii < 100; ii++)
            {
                if (!port.IsOpen)
                {
                    try
                    {
                        port.Open();
                    }
                    catch { continue; }
                }
                try
                {
                    int bytesRead = port.Read(buffer, 0, buffer.Length);
                    outStream.Write(buffer, 0, bytesRead);
                    totalRead += bytesRead;
                }
                catch (Exception e)
                {
                    if (!(e is System.TimeoutException))
                    {
                        port.Close();
                        port = new SerialPort(comPortName);
                        closes++;
                    }
                    else
                        retries++;
                }
                
            }
            port.Close();

            bt.close();
            outStream.Close();
            
#if false
            byte[] buffer = new byte[100];
            BluetoothLayer.BluetoothLayer bt = new BluetoothLayer.BluetoothLayer();
            byte[] addr = /*{0x00, 0x1f, 0xf3, 0xac, 0xa7, 0x33 };// */ {0x00, 0x14, 0xc5, 0xa1, 0x01, 0xad};
            //bt.connect(addr);
            string comPortName = bt.prepareCOMport(addr, null);
            SerialPort port = new SerialPort(comPortName);
            while (true)
            {
                if (!port.IsOpen)
                {
                    try
                    {
                        port.Open();
                    }
                    catch
                    {
                        continue;
                    }
                }
                try
                {
                    port.Read(buffer, 0, ((buffer.Length > port.BytesToRead) ? port.BytesToRead : buffer.Length));
                }
                catch (Exception e)
                {
                    Console.Out.WriteLine(e);
                    Thread.Sleep(1000);
                    port.Read(buffer, 0, buffer.Length);
                }
            }
            port.Close();
            bt.close();
#endif
        }
    }
}
