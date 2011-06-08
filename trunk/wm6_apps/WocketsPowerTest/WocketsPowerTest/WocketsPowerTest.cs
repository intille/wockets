using System;
using System.Linq;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.Runtime.InteropServices;
using System.IO;
using System.Threading;
using System.Diagnostics;

namespace Wockets
{
    public partial class WocketsPowerTest : Form
    {

        #region INTEROP

        [DllImport("coredll.dll")]
        private static extern int ShowWindow(IntPtr hWnd, int nCmdShow);
        private const int SW_MINIMIZED = 6;

        [DllImport("coredll.dll")]
        private static extern bool NLedSetDevice(int deviceId, ref NLED_SETTINGS_INFO info);
        private struct NLED_SETTINGS_INFO
        {
            public int LedNum;
            public int OffOnBlink;
            public int TotalCycleTime;
            public int OnTime;
            public int OffTime;
            public int MetaCycleOn;
            public int MetaCycleOff;
        }

        [DllImport("Coredll")]
        extern static bool CeGetUserNotificationHandles(IntPtr[] rghNotifications, int cHandles, out int pcHandlesNeeded);

        [DllImport("Coredll")]
        extern static bool CeGetUserNotification(IntPtr hNotification, int cBufferSize, out int pcBytesNeeded, IntPtr buffer);

        [DllImport("Coredll")]
        extern static bool CeClearUserNotification(IntPtr hNotification);

        [DllImport("Coredll", EntryPoint = "CeSetUserNotificationEx")]
        extern static IntPtr CeSetUserNotificationExNoType(IntPtr hNotification, ref UserNotificationTrigger pcnt, IntPtr pceun);

        struct UserNotificationTrigger
        {
            public int dwSize;
            public NotificationType dwType;
            public int dwEvent;
            public IntPtr lpszApplication;
            public IntPtr lpszArguments;
            public SystemTime stStartTime;
            public SystemTime stEndTime;
        }

        enum NotificationType : int
        {
            CNT_EVENT = 1,			//@flag CNT_EVENT  | System event notification
            CNT_TIME = 2,			//@flag CNT_TIME   | Time-based notification
            CNT_PERIOD = 3,			//@flag CNT_PERIOD | Time-based notification is active for
        }

        struct SystemTime
        {
            [DllImport("CoreDLL.dll")]
            static extern int FileTimeToSystemTime(ref long lpFileTime, ref SystemTime lpSystemTime);

            [DllImport("CoreDLL.dll")]
            static extern int FileTimeToLocalFileTime(ref long lpFileTime, ref long lpLocalFileTime);

            public ushort wYear;
            public ushort wMonth;
            public ushort wDayOfWeek;
            public ushort wDay;
            public ushort wHour;
            public ushort wMinute;
            public ushort wSecond;
            public ushort wMilliseconds;
            public static SystemTime FromDateTime(DateTime dateTime)
            {
                long fileTime = dateTime.ToFileTime();
                long localFileTime = 0;
                FileTimeToLocalFileTime(ref fileTime, ref localFileTime);
                SystemTime systemTime = new SystemTime();
                FileTimeToSystemTime(ref localFileTime, ref systemTime);
                return systemTime;
            }

            public static SystemTime FromDateTime2(DateTime dateTime)
            {
                SystemTime ret = new SystemTime();
                ret.wYear = (ushort)dateTime.Year;
                ret.wMonth = (ushort)dateTime.Month;
                ret.wDayOfWeek = (ushort)dateTime.DayOfWeek;
                ret.wDay = (ushort)dateTime.Day;
                ret.wHour = (ushort)dateTime.Hour;
                ret.wMinute = (ushort)dateTime.Minute;
                ret.wSecond = (ushort)dateTime.Second;
                ret.wMilliseconds = (ushort)dateTime.Millisecond;
                return ret;
            }
        }

        struct UserNotificationInfoHeader
        {
            public IntPtr hNotification;
            public int dwStatus;
            public IntPtr pcent;
            public IntPtr pceun;
        }

        enum NotificationFlags : int
        {
            PUN_LED = 1,       //@flag PUN_LED | LED flag.  Set if the LED should be 
            // flashed when the notification occurs.
            PUN_VIBRATE = 2,       //@flag PUN_VIBRATE | Vibrate flag.  Set if the device should
            // be vibrated.
            PUN_DIALOG = 4,       //@flag PUN_DIALOG | Dialog flag.  Set if a dialog should be
            // displayed (the app must provide title and text
            // when calling <f CeSetUserNotification>).
            PUN_SOUND = 8,      //@flag PUN_SOUND | Sound flag.  Set if the sound specified
            // in pwszSound should be played.
            PUN_REPEAT = 16,     //@flag PUN_REPEAT | Sound repeat flag.  Set if the sound
            // specified in pwszSound should be repeated progressively.
            PUN_PRIVATE = 32,     //@flag PUN_PRIVATE | Dialog box z-order flag.  Set if the
            // notification dialog box should come up behind the password.
        }

        struct UserNotificationType
        {
            public NotificationFlags ActionFlags;
            public IntPtr pwszDialogTitle;
            public IntPtr pwszDialogText;
            public IntPtr pwszSound;
            public int nMaxSound;
            public int dwReserved;
        }

        public static string CeSetUserNotificationEx(string application, string arguments, DateTime start, bool clearOld)
        {
            if (clearOld)
                UnscheduleApplicationLaunch(application);
            try
            {
                UserNotificationTrigger trigger = new UserNotificationTrigger();
                trigger.dwSize = Marshal.SizeOf(typeof(UserNotificationTrigger));
                trigger.dwType = NotificationType.CNT_TIME;
                IntPtr appBuff = Marshal.StringToBSTR(application);
                IntPtr argsBuff = Marshal.StringToBSTR(arguments);
                trigger.lpszApplication = appBuff;
                trigger.lpszArguments = argsBuff;
                trigger.stStartTime = SystemTime.FromDateTime2(start);
                IntPtr handle = CeSetUserNotificationExNoType(IntPtr.Zero, ref trigger, IntPtr.Zero);
                Marshal.FreeBSTR(appBuff);
                Marshal.FreeBSTR(argsBuff);
                return handle.ToString();
            }
            catch { return IntPtr.Zero.ToString(); }
        }

        /// <summary>
        /// Unregister an application given the path to the executable or the token that was provided
        /// </summary>
        /// <param name="applicationOrToken">The path to the application executable or the token, whichever was provided.</param>
        public static void UnscheduleApplicationLaunch(string applicationOrToken)
        {
            IntPtr handle = IntPtr.Zero;
            try { handle = FindApplicationNotification(applicationOrToken); }
            catch { }
            while (handle != IntPtr.Zero)
            {
                try { CeClearUserNotification(handle); }
                catch { }
                try { handle = FindApplicationNotification(applicationOrToken); }
                catch { }
            }
        }

        static IntPtr FindApplicationNotification(string application)
        {
            try
            {
                IntPtr[] handles = new IntPtr[100];
                int trueCount = 0;
                CeGetUserNotificationHandles(handles, handles.Length, out trueCount);
                if (trueCount > handles.Length)
                {
                    handles = new IntPtr[trueCount];
                    CeGetUserNotificationHandles(handles, handles.Length, out trueCount);
                }

                for (int i = 0; i < trueCount; i++)
                {
                    IntPtr buffer = IntPtr.Zero;
                    IntPtr handle = handles[i];
                    int bufferNeeded;
                    CeGetUserNotification(handle, 0, out bufferNeeded, buffer);
                    buffer = Marshal.AllocHGlobal(bufferNeeded);
                    CeGetUserNotification(handle, bufferNeeded, out bufferNeeded, buffer);

                    UserNotificationInfoHeader header = new UserNotificationInfoHeader();
                    //UserNotificationType type = new UserNotificationType();
                    UserNotificationTrigger trigger = new UserNotificationTrigger();
                    header = (UserNotificationInfoHeader)Marshal.PtrToStructure(buffer, typeof(UserNotificationInfoHeader));
                    trigger = (UserNotificationTrigger)Marshal.PtrToStructure(header.pcent, typeof(UserNotificationTrigger));
                    //type = (UserNotificationType)Marshal.PtrToStructure(header.pceun, typeof(UserNotificationType));
                    string appName = Marshal.PtrToStringUni(trigger.lpszApplication);
                    Marshal.FreeHGlobal(buffer);
                    if (appName != null && appName.ToLower() == application.ToLower())
                        return handle;
                }
            }
            catch { }
            return IntPtr.Zero;
        }

        [DllImport("coredll")]
        static extern IntPtr GetForegroundWindow();

        [DllImport("coredll")]
        static extern uint GetWindowThreadProcessId(IntPtr hWnd, out int lpdwProcessId);

        #endregion

        #region CONSTANTS

        private const string POWER_LOG_PATH = @"\WocketsPowerTest\";
        private const string POWER_LOG_FILE_MASK = "PowerTestTimes-{0}.csv";
        private const string DATETIME_MASK = "yyyy-MM-dd HH:mm:ss.fff";
        private const string DATE_MASK = "yyyy-MM-dd";
        private const int RETRY_FREQUENCY_IN_SECONDS = 5;

        #endregion

        #region PRIVATE MEMBERS

        private static int retryTimeCounter = 0;

        #endregion

        #region CONSTRUCTORS

        public WocketsPowerTest()
        {
            InitializeComponent();
            retryTimer.Enabled = true;
        }

        #endregion

        #region PRIVATE METHODS

        private static string logPowerTimer()
        {
            string dateString = DateTime.Today.Date.ToString(DATE_MASK);
            string powerLogPath = Path.Combine(POWER_LOG_PATH, String.Format(POWER_LOG_FILE_MASK, dateString));
            try
            {
                if (!Directory.Exists(POWER_LOG_PATH))
                {
                    Directory.CreateDirectory(POWER_LOG_PATH);
                }
                if (!File.Exists(powerLogPath))
                {
                    TextWriter twa = new StreamWriter(powerLogPath);
                    twa.WriteLine("PromptTime");
                    twa.Close();
                    Thread.Sleep(100);
                }
                dateString = DateTime.Now.ToString(DATETIME_MASK);
                TextWriter tw = new StreamWriter(powerLogPath, true);
                tw.WriteLine(dateString);
                tw.Close();
            }
            catch 
            {
                return "FAILURE TO SAVE LOG";
            }
            return dateString;
        }

        private void vibrate()
        {
            setVibrate(true);
            System.Threading.Thread.Sleep(100);
            setVibrate(false);
        }

        private void setVibrate(bool state)
        {
            NLED_SETTINGS_INFO info = new NLED_SETTINGS_INFO();
            info.LedNum = 1;
            info.OffOnBlink = state ? 1 : 0;
            try { NLedSetDevice(1, ref info); }
            catch { }
        }

        #endregion

        #region TIMER EVENTS

        private void retryTimer_Tick(object sender, EventArgs e)
        {
            retryTimer.Interval = 1000;
            retryTimeCounter += retryTimer.Interval;
            if (retryTimeCounter >= (RETRY_FREQUENCY_IN_SECONDS * retryTimer.Interval))
            {
                retryTimeCounter = 0;
                vibrate();
                head2.Text = logPowerTimer();
            }
        }

        #endregion

        private void menuItem1_Click(object sender, EventArgs e)
        {
            retryTimer.Enabled = false;
            Application.Exit();
        }


    }
}


