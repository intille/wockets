using System;
using System.Collections.Generic;
using System.Text;
using NLog;
using Winterdom.IO.FileMap;
using System.IO;
using System.Runtime.InteropServices;

namespace FileMapTestConsumer
{
    class Program
    {
        private static Logger logger = LogManager.GetLogger("ConsumerLogger");
        private static readonly uint PIPE_ACCESS_DUPLEX = 0x3;
        private static readonly uint FILE_FLAG_OVERLAPPED = 0x40000000;
        private static readonly uint PIPE_TYPE_MESSAGE = 0x4;
        private static readonly uint PIPE_NOWAIT = 0x1;
        private static readonly uint PIPE_UNLIMITED_INSTANCES = 255;

        static void Main(string[] args)
        {
            
            logger.Debug("\r\n\r\n****Starting consumer*****\r\n\r\n");
            MemoryMappedFile consumer = null;
            try
            {
                consumer = MemoryMappedFile.Open(MapAccess.FileMapAllAccess, "helloworld");
            }
            catch (NullReferenceException)
            {
                logger.Debug("Couldn't open the memory mapped file named: helloworld");
                logger.Debug("****Exiting****");
                return;
            }
            Stream consumerStream = consumer.MapView(MapAccess.FileMapRead, 0, 10);
            int readbyte = consumerStream.ReadByte();
            logger.Debug("Read: " + readbyte);
            logger.Debug("****Exiting consumer normally****");
            
            
        }

        [DllImport("coredll", SetLastError = true, EntryPoint = "CloseHandle")]
        private static extern bool WinCECloseHandle(IntPtr handle);
    }
}
