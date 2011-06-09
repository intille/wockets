using System;
using System.Linq;
using System.Collections.Generic;
using System.Windows.Forms;
using System.Runtime.InteropServices;
using System.Threading;
using System.Security.Permissions;
using System.IO;
//using Microsoft.Win32;
//using HANDLE = System.IntPtr;

namespace Wockets
{
    static class Program
    {

        #region INTEROP

        [DllImport("coredll.dll", SetLastError = true)]
        static extern int SetSystemPowerState(string psState, int StateFlags, int Options);

        const int POWER_STATE_ON = 0x00010000;
        const int POWER_STATE_OFF = 0x00020000;
        const int POWER_STATE_SUSPEND = 0x00200000;
        const int POWER_FORCE = 4096;
        const int POWER_STATE_RESET = 0x00800000;

        [DllImport("CoreDll.dll")]
        public static extern void SystemIdleTimerReset();

        public const Int32 NATIVE_ERROR_ALREADY_EXISTS = 183;

        [DllImport("coredll.dll", EntryPoint = "CreateMutex", SetLastError = true)]
        public static extern IntPtr CreateMutex(
            IntPtr lpMutexAttributes,
            bool InitialOwner,
            string MutexName);

        [DllImport("coredll.dll", EntryPoint = "ReleaseMutex", SetLastError = true)]
        public static extern bool ReleaseMutex(IntPtr hMutex);


        /* NOT CURRENTLY USED -- trying to send event to keep system from suspending
        [DllImport("coredll.dll", SetLastError = true, CallingConvention = CallingConvention.Winapi, CharSet = CharSet.Auto)]
        public static extern HANDLE CreateEvent(HANDLE lpEventAttributes, [In, MarshalAs(UnmanagedType.Bool)] bool bManualReset, [In, MarshalAs(UnmanagedType.Bool)] bool bIntialState, [In, MarshalAs(UnmanagedType.BStr)] string lpName);

        [DllImport("coredll.dll", SetLastError = true, CallingConvention = CallingConvention.Winapi, CharSet = CharSet.Auto)]
        [return: MarshalAs(UnmanagedType.Bool)]
        public static extern bool CloseHandle(HANDLE hObject);

        [DllImport("coredll.dll", SetLastError = true)]
        [return: MarshalAs(UnmanagedType.Bool)]
        public static extern bool EventModify(HANDLE hEvent, [In, MarshalAs(UnmanagedType.U4)] int dEvent);

        [DllImport("coredll.dll", SetLastError = true)]
        public static extern Int32 WaitForSingleObject(IntPtr Handle, Int32 Wait);

        private static HANDLE m_userActivityEvent;

        public enum EventFlags
        {
            PULSE = 1,
            RESET = 2,
            SET = 3
        }

        private static bool SetEvent(HANDLE hEvent)
        {
            return EventModify(hEvent, (int)EventFlags.SET);
        }

        private static bool ResetEvent(HANDLE hEvent)
        {
            return EventModify(hEvent, (int)EventFlags.RESET);
        }
        */

        /* NOT CURRENTLY USED -- Send keypress to OS to simuluate user activity and prevent system
         * from suspending
        private const byte VK_OFF = 0xDF;
        private const byte KEYEVENTF_SILENT = 0x0004;
        private const byte KEYEVENTF_KEYUP = 0x0002;

        [DllImport("coredll.dll")]
        private static extern void keybd_event(byte bVK, byte bScan, uint dwFlags, uint dwExtraInfo);
        */
        
        #endregion

        #region CONSTANTS

        public const string AUTOSTART_PARAMETER = @"AppRunAtTime";
        public const string MINIMIZED_PARAMETER = @"AppRunMinimized";
        public const string MOCK_STORAGE_LOCATION = @"\Mock Storage Card\";

        private const string WOCKETS_SUSPEND_LOCK_FOLDER = @"\Lockets\";
        private const string WOCKETS_SUSPEND_LOCK_EXTENSION = @".lckt";

        #endregion

        #region PRIVATE MEMBERS

        private static bool notdone = true;
        private static Thread stayUpThread;
        private static Thread postThread;
        //private static Thread terminateThread;

        #endregion

        #region MAIN

        /// <summary>
        /// The main entry point for the application.
        /// </summary>
        [MTAThread]
        static void Main(string[] args)
        {

            try
            {
                if (IsInstanceRunning())
                {
                    return;
                }
                SetSystemPowerState(null, POWER_STATE_ON, POWER_FORCE);
                PreventWocketsSuspension();
                SuspendPreventer.Start();
                postThread = new Thread(new ThreadStart(PostThread));
                postThread.Start();

                while (notdone)
                    Thread.Sleep(1000);
                try
                {
                    stayUpThread.Abort();
                }
                catch { }
                if (args.Length == 0)
                {
                    Application.Run(new WocketsQA(""));
                }
                else
                {
                    if (args[0].Contains(Program.AUTOSTART_PARAMETER))
                    {
                        string[] argArray = args[0].Split('|');
                        try
                        {
                            if (Convert.ToDouble(argArray[1]) >= DateTimeParsers.ConvertToUnixTimestamp(DateTime.Now.AddMinutes(-5)))
                                Application.Run(new WocketsQA(Program.AUTOSTART_PARAMETER));
                            else
                                Application.Run(new WocketsQA(Program.MINIMIZED_PARAMETER));
                        }
                        catch
                        {
                            Application.Run(new WocketsQA(Program.AUTOSTART_PARAMETER));
                        }
                    }
                    else if (args[0].Contains(Program.MINIMIZED_PARAMETER))
                    {
                        Application.Run(new WocketsQA(Program.MINIMIZED_PARAMETER));
                    }
                }
            }
            catch { }
            SuspendPreventer.Stop();
            PermitWocketsSuspension();
            System.Diagnostics.Process.GetCurrentProcess().Kill();
        }

        #endregion

        #region PUBLIC SUSPENSION METHODS

        // Call this to prevent the Wockets code from suspending the phone
        public static void PreventWocketsSuspension()
        {
            string appNameOnly = "ReflectedAppNameFailed";
            try { appNameOnly = System.Reflection.Assembly.GetExecutingAssembly().ManifestModule.Name; }
            catch { }
            string locketFileName = appNameOnly + WOCKETS_SUSPEND_LOCK_EXTENSION;
            string locketFullPath = System.IO.Path.Combine(WOCKETS_SUSPEND_LOCK_FOLDER, locketFileName);
            if (!Directory.Exists(WOCKETS_SUSPEND_LOCK_FOLDER))
                try { Directory.CreateDirectory(WOCKETS_SUSPEND_LOCK_FOLDER); }
                catch {}
            if (File.Exists(locketFullPath))
                try { File.Delete(locketFullPath); }
                catch {}
            try { File.Create(locketFullPath).Dispose(); }
            catch {}
        }

        // Call this when you are ready to allow the Wockets code to suspend the phone
        public static void PermitWocketsSuspension()
        {
            string appNameOnly = "ReflectedAppNameFailed";
            try { appNameOnly = System.Reflection.Assembly.GetExecutingAssembly().ManifestModule.Name; }
            catch { }
            string locketFileName = appNameOnly + WOCKETS_SUSPEND_LOCK_EXTENSION;
            string locketFullPath = System.IO.Path.Combine(WOCKETS_SUSPEND_LOCK_FOLDER, locketFileName);
            if (File.Exists(locketFullPath))
                try { File.Delete(locketFullPath); }
                catch { }
        }

        #endregion

        #region THREADING

        public static bool IsInstanceRunning()
        {
            IntPtr hMutex = CreateMutex(IntPtr.Zero, true, "WocketsQA");
            if (hMutex == IntPtr.Zero)
                throw new ApplicationException("Failure creating mutex: "
                    + Marshal.GetLastWin32Error().ToString("X"));
            if (Marshal.GetLastWin32Error() == NATIVE_ERROR_ALREADY_EXISTS)
                return true;
            else
                return false;
        }

        private static void PostThread()
        {
            //Here do something
            stayUpThread = new Thread(new ThreadStart(StayUp));
            stayUpThread.Start();
            notdone = false;
        }

        private static void StayUp()
        {
            while (true)
            {
                try
                {
                    SystemIdleTimerReset();
                    //KeepAwake();
                    //keybd_event(135, 0, KEYEVENTF_SILENT, 0);
                    //keybd_event(VK_OFF, 0, KEYEVENTF_SILENT | KEYEVENTF_KEYUP, 0);
                }
                catch { }
                Thread.Sleep(1000);
            }
        }
        #endregion

        #region DEPRECATED CODE

        //// Add this to Wockets if statement to check if any other applications are requesting suspension prevention
        //private static bool getIsSuspendPermitted()
        //{
        //    if (System.IO.Directory.Exists(WOCKETS_SUSPEND_LOCK_FOLDER))
        //    {
        //        try
        //        {
        //            if (System.IO.Directory.GetFiles(WOCKETS_SUSPEND_LOCK_FOLDER, "*" + WOCKETS_SUSPEND_LOCK_EXTENSION).Length >= 1)
        //                return false;
        //        }
        //        catch { }
        //    }
        //    return true;
        //}

        //public static void KeepAwake()
        //{
        //    using (RegistryKey key = Registry.LocalMachine.OpenSubKey("System\\GWE"))
        //    {
        //        object value = key.GetValue("ActivityEvent");
        //        key.Close();
        //        if (value == null) return;
        //        string activityEventName = (string)value;
        //        m_userActivityEvent = CreateEvent(HANDLE.Zero, false, true, activityEventName);
        //    }
        //    SetEvent(m_userActivityEvent);
        //}

        #endregion

    }
}