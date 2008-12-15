using System;
using System.Collections.Generic;
using System.Windows.Forms;
using WocketControlLib;
using System.IO;

namespace WocketTestProducer
{
    static class Program
    {
        /// <summary>
        /// The main entry point for the application.
        /// </summary>
        [MTAThread]
        static void Main()
        {
            /*
            MemoryMappedFile mmf1 = MemoryMappedFile.Create(null, MapProtection.PageReadWrite, 1024, "a");
            MemoryMappedFile mmf2 = MemoryMappedFile.Create(null, MapProtection.PageReadWrite, 1024, "b");
            
            Stream stream1 = mmf1.MapView(MapAccess.FileMapWrite, 0, 1024);
            Stream stream2 = mmf2.MapView(MapAccess.FileMapWrite, 0, 1024);

            Stream stream1a = mmf1.MapView(MapAccess.FileMapRead, 0, 1024);
            Stream stream2a = mmf2.MapView(MapAccess.FileMapRead, 0, 1024);

            byte[] buffer = new byte[100];
            stream1.Write(BitConverter.GetBytes(7), 0, 4);
            stream2.Write(BitConverter.GetBytes(5), 0, 4);
            stream1a.Read(buffer, 0, 4);
            int a = BitConverter.ToInt32(buffer, 0);

            stream2a.Read(buffer, 0, 4);
            int b = BitConverter.ToInt32(buffer, 0);

            stream2a.Close();
            stream1a.Close();
            stream2.Close();
            stream1.Close();
            mmf2.Close();
            mmf1.Close();
            */
            //main2();
            
            Application.Run(new ProducerForm());
        }

    }
}