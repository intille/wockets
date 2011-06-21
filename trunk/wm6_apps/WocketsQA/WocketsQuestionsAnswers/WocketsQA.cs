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
using Wockets.Utils;

namespace Wockets
{
    public partial class WocketsQA : Form
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
                    try
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
                    catch { }
                }
            
            return IntPtr.Zero;
        }

        [DllImport("coredll")]
        static extern IntPtr GetForegroundWindow();

        [DllImport("coredll")]
        static extern uint GetWindowThreadProcessId(IntPtr hWnd, out int lpdwProcessId);

        #endregion

        #region CONSTANTS

        public const string QUESTION_PATH = @"\Program Files\wockets\WocketsQA\";
        public const string QUESTION_FILE = @"WocketsQuestions.csv";
        public const string PROMPT_TIME_PATH = @"Wockets\WocketsQA\PromptTimes\";
        public const string PROMPT_TIME_FILE_MASK = "WocketsPromptTimes-{0}.csv";
        public const string ANSWER_PATH = @"Wockets\WocketsQA\";
        public const string ANSWER_DAY_FOLDER = @"AnswerLogsByHour";
        public const string ANSWER_HOUR_FOLDER = @"AnswerLogsByDay";
        public const string ANSWER_FILE_MASK = "WocketsAnswers-{0}.csv";

        // column headers

        public const string IMEI_COLUMN = @"IMEI";
        public const string SUBJECT_ID_COLUMN = @"SubjectID";
        public const string PROMPT_TIME_COLUMN = @"PromptTime";
        public const string PROMPT_TYPE_COLUMN = @"PromptType";
        public const string RESPONSE_TIME_COLUMN = @"ResponseTime";
        public const string RESPONSE_INTERVAL_START_COLUMN = @"ResponseIntervalStart";
        public const string RESPONSE_INTERVAL_END_COLUMN = @"ResponseIntervalEnd";
        public const string CATEGORIES_COLUMN = @"Categories";
        public const string SOURCE_ACTIVITIES_COLUMN = @"Activities";
        public const string PRIMARY_ACTIVITY_COLUMN = @"PrimaryActivity";
        public const string ALTERNATE_ACTIVITIES_COLUMN = @"AlternateActivities";
        public const string CLARIFICATION_QUESTION_COLUMN = @"Clarification";
        //public const string CLARIFICATION_REPONSE_COLUMN = @"ClarificationResponse";

        public const string PROMPT_TYPE_MANUAL = @"Manual";
        public const string PROMPT_TYPE_AUTOMATIC = @"Automatic";

        public const string DATETIME_MASK = "yyyy-MM-dd HH:mm:ss.fff";
        public const string DATE_MASK = "yyyy-MM-dd";

        public const string PROMPTED_INSTRUCTIONS = @"Click below to answer this question.";
        public const string PROMPTED_HEADER = @"We need your help!";
        public const string MANUAL_HEADER = @"Wockets Q + A";
        public const string MANUAL_INSTRUCTIONS = @"No questions at this time.";
        public const string COMPLETED_HEADER = @"Thanks for your help!";
        public const string COMPLETED_INSTRUCTIONS = @"";
        public const string PROMPTED_NEXT = @"Answer";
        public const string PROMPTED_HIDE = @"Dismiss";
        public const string MANUAL_NEXT = @"Ask me now";
        public const string MANUAL_HIDE = @"Hide";
        public const string OTHER_ACTIVITY = @"Other";

        public const int EARLIEST_PROMPT_HOUR = 14;
        public const int LATEST_PROMPT_HOUR = 16;
        public const int PROMPTS_PER_DAY = 20;
        public const int RETRY_TIMEOUT_IN_SECONDS = 300;
        public const int RETRY_COUNT = 2;

        #endregion

        #region PUBLIC MEMBERS

        public static WocketsQACategories wqaCategories;
        public static WocketsQAWinnow wqaWinnow;
        public static WocketsQAClarification wqaClarification;
        public static DataTable QuestionTable;
        public static DataTable AnswerTable;

        public static List<string> SelectedCategoriesList = new List<string>();
        public static List<string> SelectedActivitiesList = new List<string>();

        public static int RetryTimeCounter = 0;
        public static int RetryCount = 0;
        public static bool Done = false;

        #endregion

        #region PRIVATE MEMBERS

        private static List<DateTime> promptTimes = new List<DateTime>();
        private static bool isAutoPrompt = false;

        #endregion

        #region CONSTRUCTORS

        public WocketsQA(string argument)
        {
            InitializeComponent();
            loadPromptTimes();
            if (argument == Program.MINIMIZED_PARAMETER)
            {
                Application.Exit();
            }
            initializePages();
            initializeQuestionTable();
            initializeAnswerTable();
            RetryCount = getRetryCount();
            if (argument == Program.AUTOSTART_PARAMETER)
            {
                isAutoPrompt = true;
                head1.Text = PROMPTED_HEADER;
                head2.Text = PROMPTED_INSTRUCTIONS;
                menuLeft.Text = PROMPTED_HIDE;
                menuRight.Text = PROMPTED_NEXT;
                LogResponse(PROMPT_TIME_COLUMN, DateTime.Now.Subtract(new TimeSpan(0, 0, RetryCount * RETRY_TIMEOUT_IN_SECONDS)).ToString(DATETIME_MASK), false);
                LogResponse(PROMPT_TYPE_COLUMN, PROMPT_TYPE_AUTOMATIC, false);
            }
            this.WindowState = FormWindowState.Maximized;
            if (argument == Program.AUTOSTART_PARAMETER)
            {
                raisePrompt();
            }
        }

        #endregion

        #region INITIALIZATION METHODS

        private void initializeQuestionTable()
        {
            QuestionTable = loadDataTable(Path.Combine(QUESTION_PATH, QUESTION_FILE));
            if (QuestionTable.Rows.Count < 1)
                head2.Text = @"No questions found.";
        }

        private void initializePages()
        {
            wqaCategories = new WocketsQACategories();
            wqaWinnow = new WocketsQAWinnow();
            wqaClarification = new WocketsQAClarification();
        }

        private void initializeAnswerTable()
        {
            AnswerTable = new DataTable();
            AnswerTable.Columns.Add(IMEI_COLUMN);
            AnswerTable.Columns.Add(SUBJECT_ID_COLUMN);
            AnswerTable.Columns.Add(PROMPT_TIME_COLUMN);
            AnswerTable.Columns.Add(PROMPT_TYPE_COLUMN);
            AnswerTable.Columns.Add(RESPONSE_TIME_COLUMN);
            AnswerTable.Columns.Add(RESPONSE_INTERVAL_START_COLUMN);
            AnswerTable.Columns.Add(RESPONSE_INTERVAL_END_COLUMN);
            AnswerTable.Columns.Add(CATEGORIES_COLUMN);
            AnswerTable.Columns.Add(PRIMARY_ACTIVITY_COLUMN);
            AnswerTable.Columns.Add(ALTERNATE_ACTIVITIES_COLUMN);
            //AnswerTable.Columns.Add(CLARIFICATION_REPONSE_COLUMN);
        }

        private void initializeFarewellView()
        {
            this.head2.Text = "";
            this.menuLeft.Text = MANUAL_HIDE;
            this.menuRight.Text = "";
            this.menuRight.Enabled = false;
        }

        public static void InitializeClarifications()
        {
            if (WocketsQA.SelectedCategoriesList.Count > 0)
            {
                WocketsQA.wqaClarification.InitializeClarification(0);
                WocketsQA.wqaClarification.Show();
            }
            else
            {
                WocketsQA.HideAllPages();
            }
        }

        #endregion

        #region PUBLIC METHODS

        public static void ScheduleRetry()
        {
            ScheduleRetry(RETRY_TIMEOUT_IN_SECONDS);
        }

        public static void ScheduleRetry(int secondsToRetry)
        {
            if (RetryCount <= RETRY_COUNT && isAutoPrompt)
            {
                try
                {
                    File.Create(RetryCount.ToString() + ".retry");
                    schedulePrompt(secondsToRetry);
                }
                catch { }
            }
        }

        public static void SchedulePrompts()
        {
            string appName = System.Reflection.Assembly.GetExecutingAssembly().GetName().CodeBase;
            try { UnscheduleApplicationLaunch(appName); }
            catch { }

            int secondsUntilPrompt = -1;
            for (int i = 0; i < promptTimes.Count - 1; i++)
            {
                if (promptTimes[i] > DateTime.Now.AddMinutes(1))
                {
                    TimeSpan ts = promptTimes[i].Subtract(DateTime.Now);
                    secondsUntilPrompt = (int)ts.TotalSeconds;
                    schedulePrompt(secondsUntilPrompt);
                }
            }
            if (secondsUntilPrompt < 0)
            {
                generatePromptTimes();
                SchedulePrompts();
            }
        }

        public static void HideAllPages()
        {
            wqaCategories.Hide();
            wqaWinnow.Hide();
            wqaClarification.Hide();
        }

        #endregion

        #region PRIVATE FUNCTIONS

        private int getRetryCount()
        {
            int retry = 0;
            try
            {
                string[] retries = Directory.GetFiles(".", "*.retry");
                foreach (string s in retries)
                {
                    try { File.Delete(s); }
                    catch { }
                    string thisRetry = Path.GetFileNameWithoutExtension(s);
                    if (Convert.ToInt32(thisRetry) > retry)
                        retry = Convert.ToInt32(thisRetry);
                }
            }
            catch
            {
                retry = RETRY_COUNT + 1;
            }
            return retry;
        }

        private static string getStorageCard()
        {
            String path = Program.MOCK_STORAGE_LOCATION;
            {
                string firstCard = "";
                try
                {
                    System.IO.DirectoryInfo di = new System.IO.DirectoryInfo("\\");
                    System.IO.FileSystemInfo[] fsi = di.GetFileSystemInfos();
                    //iterate through them
                    for (int x = 0; x < fsi.Length; x++)
                    {
                        //check to see if this is a temporary storage card (e.g. SD card)
                        if ((fsi[x].Attributes & System.IO.FileAttributes.Temporary) == System.IO.FileAttributes.Temporary)
                        {
                            path = fsi[x].FullName;
                            try
                            {
                                Directory.CreateDirectory(firstCard + "\\writable");
                                Directory.Delete(firstCard + "\\writable");
                            }
                            catch (Exception)
                            {
                                path = Program.MOCK_STORAGE_LOCATION;
                                continue;
                            }
                            //if so, return the path
                            break;
                        }
                    }
                }
                catch { }
            }
            return path;
        }

        private DataTable loadDataTable(string fileName)
        {
            DataTable dTable = CSVParser.LoadCSV(fileName);
            try { dTable.PrimaryKey = new DataColumn[] { dTable.Columns[0] }; }
            catch { }
            return dTable;
        }

        #endregion

        #region PRIVATE METHODS

        private static void generatePromptTimes()
        {
            promptTimes.Clear();
            double chunksize = (LATEST_PROMPT_HOUR - EARLIEST_PROMPT_HOUR) / (double)PROMPTS_PER_DAY;
            Random random = new Random();
            DateTime start = new DateTime(DateTime.Today.Year, DateTime.Today.Month, DateTime.Today.Day, EARLIEST_PROMPT_HOUR, 0, 0);
            for (int j = 0; j <= 1; j++)
            {
                start = start.AddDays(j);
                for (int i = 0; i < PROMPTS_PER_DAY; i++)
                    promptTimes.Add(start.AddHours((random.NextDouble() * chunksize) + (chunksize * i)));
            }
            sortPrompts();
            string dateString = DateTime.Today.Date.ToString(DATE_MASK);
            string storageCard = getStorageCard();
            string promptTimePath = Path.Combine(storageCard, PROMPT_TIME_PATH);
            string promptPath = Path.Combine(promptTimePath, String.Format(PROMPT_TIME_FILE_MASK, dateString));
            try
            {
                if (!Directory.Exists(promptTimePath))
                {
                    Directory.CreateDirectory(promptTimePath);
                }
                if (File.Exists(promptPath))
                    File.Delete(promptPath);
                if (!File.Exists(promptPath))
                {
                    TextWriter tw = new StreamWriter(promptPath, true);
                    tw.WriteLine("PromptTime");
                    foreach (DateTime dt in promptTimes)
                        tw.WriteLine(dt.ToString(DateTimeParsers.DATETIME_MASK));
                    tw.Close();
                }
            }
            catch { }
        }

        private static void loadPromptTimes()
        {
            promptTimes.Clear();
            string dateString = DateTime.Today.Date.ToString(DATE_MASK);
            string storageCard = getStorageCard();
            string promptTimePath = Path.Combine(storageCard, PROMPT_TIME_PATH);
            string promptPath = Path.Combine(promptTimePath, String.Format(PROMPT_TIME_FILE_MASK, dateString));
            if (File.Exists(promptPath))
            {
                try
                {
                    DataTable dTable = CSVParser.LoadCSV(promptPath);
                    foreach (DataRow dr in dTable.Rows)
                    {
                        if (DateTimeParsers.DateTimeParse(dr[0].ToString()) > DateTime.Now)
                        {
                            promptTimes.Add(DateTimeParsers.DateTimeParse(dr[0].ToString()));
                        }
                    }
                    sortPrompts();
                    SchedulePrompts();
                    return;
                }
                catch {  }
            }
            generatePromptTimes();
            SchedulePrompts();
        }

        private static void sortPrompts()
        {
            promptTimes.TrimExcess();
            promptTimes.Sort();
        }

        private static void schedulePrompt(int secondsFromNow)
        {
            string appName = System.Reflection.Assembly.GetExecutingAssembly().GetName().CodeBase;
            //string appNameOnly = System.Reflection.Assembly.GetExecutingAssembly().ManifestModule.Name;
            System.DateTime dt = DateTime.Now.AddSeconds(secondsFromNow);
            string args = "AppRunAtTime" + "|" + DateTimeParsers.ConvertToUnixTimestamp(dt).ToString();
            try { string Result = CeSetUserNotificationEx(appName, args, dt, false); }
            catch (Exception e) { MessageBox.Show(e.ToString()); }
        }

        private void showPrompt()
        {
            this.head1.Text = COMPLETED_HEADER;
            this.head2.Text = COMPLETED_INSTRUCTIONS;
            this.menuLeft.Text = MANUAL_HIDE;
            this.menuRight.Text = MANUAL_NEXT;
            initializePages();
            wqaCategories.initializeListView();
            wqaCategories.Show();
            DateTime responseTime = DateTime.Now;
            WocketsQA.LogResponse(WocketsQA.RESPONSE_TIME_COLUMN, responseTime.ToString(DateTimeParsers.DATETIME_MASK), false);
            WocketsQA.LogResponse(WocketsQA.RESPONSE_INTERVAL_END_COLUMN, responseTime.ToString(DateTimeParsers.DATETIME_MASK), false);
            WocketsQA.LogResponse(WocketsQA.RESPONSE_INTERVAL_START_COLUMN, responseTime.Subtract(new TimeSpan(0, 10, 0)).ToString(DateTimeParsers.DATETIME_MASK), false);
        }

        private void raisePrompt()
        {
            vibrate();
            playSoundFromResource();
        }

        private void playSoundFromResource()
        {
            try
            {
                System.IO.Stream audioStream = new MemoryStream(Properties.Resources.PromptSound);
                System.Media.SoundPlayer player = new System.Media.SoundPlayer(audioStream);
                player.PlaySync();
            }
            catch { }
        }

        private void vibrate()
        {
            setVibrate(true);
            System.Threading.Thread.Sleep(100);
            setVibrate(false);
            System.Threading.Thread.Sleep(100);
            setVibrate(true);
            System.Threading.Thread.Sleep(150);
            setVibrate(false);
            System.Threading.Thread.Sleep(100);
            setVibrate(true);
            System.Threading.Thread.Sleep(200);
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

        #region PUBLIC METHODS

        public static void LogResponse(string column, string value, bool append)
        {
            if (AnswerTable.Rows.Count < 1)
                AnswerTable.Rows.Add();
            int row = AnswerTable.Rows.Count - 1;
            if (AnswerTable.Rows[row][column].ToString() == "" || !append)
                AnswerTable.Rows[row][column] = value;
            else
                AnswerTable.Rows[row][column] = AnswerTable.Rows[row][column].ToString() + "|" + value;
        }

        public static void SaveDataLog()
        {
            try
            {
                string dateString = DateTime.Today.Date.ToString(DATE_MASK);
                //string hourString = DateTime.Now.ToString("HH");
                string storageCard = getStorageCard();
                string answerPath = Path.Combine(storageCard, ANSWER_PATH);
                string[] logPath =
                {
                    Path.Combine(Path.Combine(answerPath, ANSWER_HOUR_FOLDER), String.Format(ANSWER_FILE_MASK, dateString)),
                    //Path.Combine(Path.Combine(ANSWER_PATH, ANSWER_DAY_FOLDER), String.Format(ANSWER_FILE_MASK, dateString + "-" + hourString))
                };
                foreach (string s in logPath)
                {            
                    if (!Directory.Exists(Path.GetDirectoryName(s)))
                    {
                        Directory.CreateDirectory(Path.GetDirectoryName(s));
                    }
                    if (!File.Exists(s))
                    {
                        TextWriter twa = new StreamWriter(s, true);
                        foreach (DataColumn dc in AnswerTable.Columns)
                            twa.Write(dc.ColumnName + ",");
                        twa.WriteLine();
                        twa.Close();
                    }
                    TextWriter tw = new StreamWriter(s, true);
                    for (int i = 0; i < AnswerTable.Rows.Count; i++)
                    {
                        foreach (DataColumn dc in AnswerTable.Columns)
                        {
                            tw.Write(AnswerTable.Rows[i][dc] + ",");
                        }
                        tw.WriteLine();
                    }
                    tw.Close();
                }
                //Initialize the upload logger
                Wockets.Utils.CustomSynchronizedLogger UploadQAEvents = new CustomSynchronizedLogger("qa");
                //Generate log string
                for (int i = 0; i < AnswerTable.Rows.Count; i++)
                {
                    string event_status_log = "";
                    //Omit first two columns to be  compatible with updater.
                    for (int j = 2; j < AnswerTable.Columns.Count; j++)
                    {
                        event_status_log += AnswerTable.Rows[i][j];
                        if (j < AnswerTable.Columns.Count - 1) event_status_log += ",";
                    }
                    UploadQAEvents.Write(event_status_log);
                }
                //Thread.Sleep(1000);
                //Terminate the upload logger
                UploadQAEvents.Flush();

                AnswerTable.Rows.Clear();
            }
            catch { }
        }

        #endregion

        #region OVERRIDES

        protected override void OnDeactivate(EventArgs e)
        {
            base.OnDeactivate(e);

            //if the foreground window was not created by this application, exit this application
            IntPtr foregroundWindow = GetForegroundWindow();
            int foregroundProcId;
            GetWindowThreadProcessId(foregroundWindow, out foregroundProcId);
            using (Process currentProc = Process.GetCurrentProcess())
            {
                if (foregroundProcId != currentProc.Id)
                {
                    WocketsQA.ScheduleRetry();
                    WocketsQA.SaveDataLog();
                    Application.Exit();
                }
            }
        }

        #endregion

        #region TIMER EVENTS

        private void retryTimer_Tick(object sender, EventArgs e)
        {
            RetryTimeCounter += retryTimer.Interval;
            if (RetryTimeCounter >= (RETRY_TIMEOUT_IN_SECONDS * 1000) - 60000)
            {
                retryTimer.Enabled = false;
                RetryCount++;
                int nextTime = (int)(((RETRY_TIMEOUT_IN_SECONDS * 1000) - RetryTimeCounter) / 1000);
                ScheduleRetry(nextTime);
                WocketsQA.SaveDataLog();
                Application.Exit();
            }
        }

        #endregion

        #region MENU EVENTS

        private void menuLeft_Click(object sender, EventArgs e)
        {

            try
            {
                WocketsQA.LogResponse(WocketsQA.PRIMARY_ACTIVITY_COLUMN, "X", false);
            }
            catch { }
            Program.PermitWocketsSuspension();
            WocketsQA.SaveDataLog();
            Application.Exit();
        }

        private void menuRight_Click(object sender, EventArgs e)
        {
            if (menuRight.Text == MANUAL_NEXT)
            {
                WocketsQA.LogResponse(WocketsQA.PROMPT_TYPE_COLUMN, PROMPT_TYPE_MANUAL, false);
                WocketsQA.LogResponse(WocketsQA.PROMPT_TIME_COLUMN, DateTime.Now.ToString(DATETIME_MASK), false);
            }
            else
            {
                LogResponse(PROMPT_TYPE_COLUMN, PROMPT_TYPE_AUTOMATIC, false);
            }
            showPrompt();
            initializeFarewellView();
        }

        #endregion

        #region FORM EVENTS

        private void WocketsQA_GotFocus(object sender, EventArgs e)
        {
            this.WindowState = FormWindowState.Maximized;
        }

        private void WocketsQA_Load(object sender, EventArgs e)
        {
            this.WindowState = FormWindowState.Maximized;
        }

        private void WocketsQA_Activated(object sender, EventArgs e)
        {
            this.WindowState = FormWindowState.Maximized;
            WocketsQA.RetryTimeCounter = 0;
        }

        #endregion

    }
}


