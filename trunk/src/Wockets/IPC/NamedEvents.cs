using System;
using System.Runtime.InteropServices;
using System.Threading;
using HANDLE = System.IntPtr;

namespace Wockets.IPC
{
    public class NamedEvents
    {
        [DllImport("coredll.dll", SetLastError = true, CallingConvention = CallingConvention.Winapi, CharSet = CharSet.Auto)]
        public static extern HANDLE CreateEvent(HANDLE lpEventAttributes, [In, MarshalAs(UnmanagedType.Bool)] bool bManualReset, [In, MarshalAs(UnmanagedType.Bool)] bool bIntialState, [In, MarshalAs(UnmanagedType.BStr)] string lpName);

        [DllImport("coredll.dll", SetLastError = true, CallingConvention = CallingConvention.Winapi, CharSet = CharSet.Auto)]
        [return: MarshalAs(UnmanagedType.Bool)]
        public static extern bool CloseHandle(HANDLE hObject);

        [DllImport("coredll.dll", SetLastError = true)]
        public static extern Int32 WaitForSingleObject(IntPtr Handle, UInt32 Wait);

        [DllImport("coredll.dll", SetLastError = true)]
        [return: MarshalAs(UnmanagedType.Bool)]
        public static extern bool EventModify(HANDLE hEvent, [In, MarshalAs(UnmanagedType.U4)] int dEvent);
        public enum EventFlags
        {
            PULSE = 1,
            RESET = 2,
            SET = 3
        }

        const UInt32 INFINITE = 0xFFFFFFFF;
        const UInt32 WAIT_ABANDONED = 0x00000080;
        const UInt32 WAIT_OBJECT_0 = 0x00000000;
        const UInt32 WAIT_TIMEOUT = 0x00000102;

        private bool SetEvent(HANDLE hEvent)
        {
            return EventModify(hEvent, (int)EventFlags.SET);
        }
        private bool ResetEvent(HANDLE hEvent)
        {
            return EventModify(hEvent, (int)EventFlags.RESET);
        }

        HANDLE p;
        public void Send(string name)
        {
            p = CreateEvent(HANDLE.Zero, true, false, name);
            SetEvent(p);
            Thread.Sleep(500);
            CloseHandle(p);
        }

        public void Receive(string name)
        {
            p = CreateEvent(HANDLE.Zero, true, false, name);
            // Catch the event
            WaitForSingleObject(p, INFINITE);         
            //SetEvent(p);           
        }

        public void Reset()
        {
            ResetEvent(p);
            Thread.Sleep(500);
            CloseHandle(p);
        }
    }
}
