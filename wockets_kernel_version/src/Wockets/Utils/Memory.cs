using System;

using System.Collections.Generic;
using System.Text;
using System.Runtime.InteropServices;

namespace Wockets.Utils
{
    public struct DiskSpace
    {
        public ulong FreeBytesAvailable;
        public ulong TotalNumberOfBytes;
        public ulong TotalNumberOfFreeBytes;
    };

    public class Memory
    {
        [DllImport("coredll.dll", SetLastError = true, CharSet = CharSet.Auto)]
        [return: MarshalAs(UnmanagedType.Bool)]
        static extern bool GetDiskFreeSpaceEx(string lpDirectoryName,
        out ulong lpFreeBytesAvailable,
        out ulong lpTotalNumberOfBytes,
        out ulong lpTotalNumberOfFreeBytes);

        public static DiskSpace GetDiskSpace(string directory)
        {
            DiskSpace space;
            bool success = GetDiskFreeSpaceEx(directory, out space.FreeBytesAvailable, out space.TotalNumberOfBytes,
                   out space.TotalNumberOfFreeBytes);
            return space;
        }
    }
}
