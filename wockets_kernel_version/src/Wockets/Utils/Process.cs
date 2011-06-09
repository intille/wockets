using System;

using System.Runtime.InteropServices;

namespace Wockets.Utils
{
    public class Process
    {
        const int SYS_HANDLE_BASE = 64;
        const int SH_WIN32 = 0;
        const int SH_CURTHREAD = 1;
        const int SH_CURPROC = 2;
        const uint SYSHANDLE_OFFSET = 0x004;
        const uint PUserKDataARM = 0xFFFFC800;
        const uint PUserKDataX86 = 0x00005800;

        public static int GetCurrentProcessID()
        {
            uint PUserKData = GetCPUArchitecture() == PROCESSOR_ARCHITECTURE.PROCESSOR_ARCHITECTURE_ARM ? PUserKDataARM : PUserKDataX86;
            IntPtr pBase = new IntPtr((int)(PUserKData + SYSHANDLE_OFFSET));
            return Marshal.ReadInt32(pBase, SH_CURTHREAD * 4);
        }

        public static int GetCurrentThreadID()
        {
            uint PUserKData = GetCPUArchitecture() == PROCESSOR_ARCHITECTURE.PROCESSOR_ARCHITECTURE_ARM ? PUserKDataARM : PUserKDataX86;
            IntPtr pBase = new IntPtr((int)(PUserKData + SYSHANDLE_OFFSET));
            return Marshal.ReadInt32(pBase, SH_CURPROC * 4);
        }

        public static IntPtr GetCurrentProcess()
        {
            return new IntPtr(SH_CURPROC + SYS_HANDLE_BASE);
        }

        public static IntPtr GetCurrentThread()
        {
            return new IntPtr(SH_CURTHREAD + SYS_HANDLE_BASE);
        }

        public static PROCESSOR_ARCHITECTURE GetCPUArchitecture()
        {
            SYSTEM_INFO si = new SYSTEM_INFO();
            GetSystemInfo(ref si);
            return (PROCESSOR_ARCHITECTURE)si.wProcessorArchitecture;
        }

        public enum PROCESSOR_ARCHITECTURE
        {
            PROCESSOR_ARCHITECTURE_INTEL = 0,
            PROCESSOR_ARCHITECTURE_MIPS = 1,
            PROCESSOR_ARCHITECTURE_ALPHA = 2,
            PROCESSOR_ARCHITECTURE_PPC = 3,
            PROCESSOR_ARCHITECTURE_SHX = 4,
            PROCESSOR_ARCHITECTURE_ARM = 5,
            PROCESSOR_ARCHITECTURE_IA64 = 6,
            PROCESSOR_ARCHITECTURE_ALPHA64 = 7,
            PROCESSOR_ARCHITECTURE_UNKNOWN = 0xFFFF,
        }
        [DllImport("Coredll")]
        public static extern void GetSystemInfo(ref SYSTEM_INFO SystemInfo);

        [DllImport("Coredll")]
        public static extern int GetThreadPriority(
            IntPtr hThread);

        [DllImport("Coredll")]
        public static extern bool GetThreadTimes(
            IntPtr hThread,
            out long lpCreationTime,
            out long lpExitTime,
            out long lpKernelTime,
            out long lpUserTime);

    }
    public struct SYSTEM_INFO
    {
        public ushort wProcessorArchitecture;
        public ushort wReserved;
        public uint dwPageSize;
        public int lpMinimumApplicationAddress;
        public int lpMaximumApplicationAddress;
        public uint dwActiveProcessorMask;
        public uint dwNumberOfProcessors;
        public uint dwProcessorType;
        public uint dwAllocationGranularity;
        public ushort wProcessorLevel;
        public ushort wProcessorRevision;
    }

}
