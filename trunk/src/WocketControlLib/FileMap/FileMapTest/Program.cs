using System;
using System.Collections.Generic;
using System.Text;
using Winterdom.IO.FileMap.Tests;
using Winterdom.IO.FileMap;
using System.IO;
using NLog;
using System.Threading;

namespace FileMapTest
{
    class Program
    {
        private static Logger logger = LogManager.GetLogger("FileMapTest");

        static void Main(string[] args)
        {
            /*
            FileMapTests tester = new FileMapTests();
            tester.TestMMFFileWrite();
            tester.TestMMFViewSeeking();
            tester.TestMMFViewSize();
            tester.TestNamedMMF();
            tester.TestNonBackedMMF();
            */
            logger.Debug("\r\n\r\n********Starting FileMapTest*******\r\n\r\n");
            

            MemoryMappedFile mmf = MemoryMappedFile.Create(MapProtection.PageReadWrite, 10L, "helloworld");
          //  MemoryMappedFile mmf2 = MemoryMappedFile.Open(MapAccess.FileMapAllAccess, "helloworld");
            Stream stream1 = mmf.MapView(MapAccess.FileMapWrite, 0, 9);
            logger.Debug("Writing to the stream");
            // Stream stream2 = mmf2.MapView(MapAccess.FileMapRead, 0, 10);
            stream1.WriteByte(12);
            logger.Debug("Done writing, sleeping for 60 seconds");
            Thread.Sleep(60000);
           // int read = stream2.ReadByte();
           // if (read == 12)
           //     logger.Debug("Read the correct byte");
          //  else
           //     logger.Debug("Read the INcorrect byte!");
            stream1.Close();
           // stream2.Close();
            mmf.Close();
           // mmf2.Close();
            logger.Debug("****Exiting FileMapTest normally*****");
        }
    }
}
