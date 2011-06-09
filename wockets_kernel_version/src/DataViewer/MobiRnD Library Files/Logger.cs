using System;
using System.IO;
using System.Runtime.InteropServices;

using System.Reflection; //for version
using System.Globalization; //culture info
using System.Text;//StringBuilder for log to buffer

using MobiRnD_RDT.Utilities; //CompareFileWriteTime

namespace MobiRnD_RDT.Logging
{

	/// <summary>
	/// Summary description for Logger.
	/// </summary>
	public class Logger
    {
        #region ENUMs
        public enum LogLevels { DEBUG, INFO, WARNING, ERROR };
        #endregion

        #region CONSTANT NEWLINE
#if (Smartphone || PocketPC)
        public static string NEWLINE  = Microsoft.VisualBasic.ControlChars.NewLine;
#else
        public static string NEWLINE = Environment.NewLine;
#endif
        #endregion


        #region FIELDs

        #region LOG LOCATION
        private static string _parentDirectory = "";
        private static string _defaultLogName = "log";
        private static string _extension = ".txt";
        private static bool _savesInLogsFolder = true;
        #endregion

        #region FILE CREATION
        private static bool _isLoggingByDay = false;
        private static bool _isLoggingByHour = false;
        private static bool _isLimitingSize = false;
        private static int _kbSizeLimit = 100;
        private static bool _deletesOldLogs = true;
        private static int _keepLogCount = 10;
        #endregion

        #region LOG METHOD
        private static bool _isLoggingToBuffer = false;
        private static bool _writesBufferToFileOnError = true;
        private static int _flushFrequency = 0; //write everytime if 0
        private static bool _isLoggingToConsole = false;
        private static LogLevels _logLevel = LogLevels.INFO;
        #endregion

        #region LOG DETAILS
        private static bool _isIncludingHeader = true;
        private static bool _isIncludingSystemInfo = false;
        #endregion
        #endregion

        #region LOG VARIABLES
        private static FileStream _fs = null;
        private static StreamWriter _sw = null;
        private static StringBuilder _sb = null;
        private static int _countWrites = 0;
        private static string _pathCurrentLog = "";
        private static long _lastTick = Environment.TickCount;
        #endregion

        #region PROPERTIES
        #region LOG LOCATION
        public static string ParentDirectory
        {
            get { return _parentDirectory; }
            set { _parentDirectory = value; }
        }
        public static string DefaultLogName
        {
            get { return _defaultLogName; }
            set { _defaultLogName = value; }
        }
        public static string LogExtension
        {
            get { return _extension; }
            set { _extension = value; }
        }
        public static bool SavesInLogsSubfolder
        {
            get { return _savesInLogsFolder; }
            set { _savesInLogsFolder = value; }
        }        
        #endregion

        #region FILE CREATION

        /// <summary>
        /// Logger groups log requests by day, creating a new log file if a log request begins on a new day
        /// Files are suffixed with _YYYY_MM_DD (4-digit year, 2-digit month, 2-digit day)
        /// </summary>
        public static bool IsLoggingByDay
        {
            get { return _isLoggingByDay; }
            set { _isLoggingByDay = value; }
        }

        /// <summary>
        /// Logger groups log requests by hour, creating a new log file if a log request begins on a new hour
        /// Files are suffixed with _YYYY_MM_DD_HH (4-digit year, 2-digit month, 2-digit day, 2-digit hour)
        /// </summary>
        public static bool IsLoggingByHour
        {
            get { return _isLoggingByHour; }
            set { _isLoggingByHour = value; }
        }
        /// <summary>
        /// If current log file exceeds KbSizeLimit, file is renamed with _YYYY_MM_DD_HH_MM_SS suffix 
        /// (4-digit year, 2-digit month, 2-digit day, 2-digit hour, 2-digit minute, 2-digit second)
        /// and a new file is started
        /// </summary>
        public static bool IsLimitingSize
        {
            get { return _isLimitingSize; }
            set { _isLimitingSize = value; }
        }
         
        /// <summary>
        /// Used if IsLimitingSize=true
        /// If current log file exceeds KbSizeLimit, file is renamed with _YYYY_MM_DD_HH_MM_SS suffix 
        /// </summary>
        public static int KbSizeLimit
        {
            get { return _kbSizeLimit; }
            set { _kbSizeLimit = value; }
        }

        /// <summary>
        /// If true, Logger counts number of log files in the log directory
        /// if it is greater than MaximumLogCount, the oldest logs are deleted, until the number of files is within this parameter
        /// </summary>
        public static bool DeletesOldLogs
        {
            get { return _deletesOldLogs; }
            set { _deletesOldLogs = value; }
        }

        /// <summary>
        /// Used if DeletesOldLogs is true
        /// If the number of log files in the log directory exceeds this number, the oldest files are deleted until the number of files is within this parameter
        /// </summary>
        public static int MaximumLogCount
        {
            get { return _keepLogCount; }
            set { _keepLogCount = value; }
        }
        #endregion

        #region LOG METHOD
        /// <summary>
        /// If true, Logger writes to a buffer (StringBuilder) until an explicit call is made to WriteBufferToFile
        /// If WritesBufferToFileOnError is true, buffer will also be written to file when an error is logged
        /// </summary>
        public static bool IsLoggingToBuffer
        {
            get { return _isLoggingToBuffer; }
            set { _isLoggingToBuffer = value; }
        }

        /// <summary>
        /// Used when IsLoggingToBuffer is true
        /// If true, buffer will be written to file when an error is logged
        /// </summary>
        public static bool WritesBufferToFileOnError        
        {
            get { return _writesBufferToFileOnError; }
            set { _writesBufferToFileOnError = value; }
        }

        /// <summary>
        /// Logger will write out to file every for every FlushFrequency log requests
        /// If FlushFrequency=0, Logger writes to file every time
        /// </summary>
        public static int FlushFrequency
        {
            get { return _flushFrequency; }
            set { _flushFrequency = value; }
        }

        /// <summary>
        /// Uses Console.Write to also log to console - useful when debugging on PC only
        /// </summary>
        public static bool IsLoggingToConsole
        {
            get { return _isLoggingToConsole; }
            set {  _isLoggingToConsole = value; }
        }

        /// <summary>
        /// Logger only logs messages at a log level set to MinimumLogLevel or above
        /// </summary>
        /// <example>MinumumLogLevel=LogLevels.Info -> logs messages at LogLevels.Info, LogLevels.Warning, and LogLevels.Error, but not LogLevels.Debug</example>
        public static LogLevels MinimumLogLevel
        {
            get { return _logLevel; }
            set { _logLevel = value; }
        }
        #endregion

        #region LOG DETAILS
        /// <summary>
        /// For each new log file, prepends information about the application and system, including:
        /// application name; application version; machine name
        /// screen width and height
        /// OS version and name; .NET Framework version; culture language
        /// culture date format; culture time format; local date; universal date
        /// </summary>
        public static bool IsIncludingHeader
        {
            get { return _isIncludingHeader; }
            set { _isIncludingHeader = value; }
        }

        /// <summary>
        /// Logs memory and battery status information with each request
        /// Only used in mobile device logging right now (not on PC)
        /// </summary>
        public static bool IsIncludingSystemInfo
        {
            get { return _isIncludingSystemInfo; }
            set { _isIncludingSystemInfo = value; }
        }
        #endregion
        #endregion

        #region GET APPLICATION ATTRIBUTES
        /// <summary>
        /// Retrieves the version of the calling assembly, which is set in the AssemblyInfo.cs file
        /// This method allows you to send a specific assembly (usually retrieved with Assembly.GetCallingAssembly())
        /// </summary>
        /// <returns>String version of calling assembly</returns>
        public static string GetApplicationVersion(Assembly callingAssembly)
        {
            AssemblyName assemblyname = callingAssembly.GetName();
            Version assemblyver = assemblyname.Version;
            return assemblyver.ToString();
        }
        /// <summary>
        /// Retrieves the version of the executing assembly, which is set in the AssemblyInfo.cs file
        /// </summary>
        /// <returns>String version of executing assembly</returns>
        public static string GetLoggerVersion()
        {
            return GetApplicationVersion(Assembly.GetExecutingAssembly());
        }

        /// <summary>
        /// Retrieves the version of the calling assembly, which is set in the AssemblyInfo.cs file
        /// </summary>
        /// <returns>String version of calling assembly</returns>
        public static string GetCallingApplicationVersion()
        {
            return GetApplicationVersion(Assembly.GetCallingAssembly());
        }

        /// <summary>
        /// Retrieves the version of the entry assembly, which is set in the AssemblyInfo.cs file
        /// </summary>
        /// <returns>String version of entry assembly</returns>
        public static string GetApplicationVersion()
        {
#if (Smartphone || PocketPC)
            return GetApplicationVersion(Assembly.GetCallingAssembly());
#else
            return GetApplicationVersion(Assembly.GetEntryAssembly());
#endif
        }

        /// <summary>
        /// Uses the environment variable to retrieve the name of the computer
        /// </summary>
        /// <returns>The name of the computer or "phone"</returns>
        public static string GetMachineName()
        {
            string machinename = "";
#if (!Smartphone && !PocketPC)
            try
            {
                machinename = Environment.MachineName;
            }
            catch { }
#else
			machinename ="PHONE";
#endif

            return machinename;
        }


        /// <summary>
        /// Retrieves the name of the passed assembly
        /// </summary>
        /// <param name="callingAssembly">Assembly.GetCallingAssembly();</param>
        /// <returns>Assembly name</returns>
        public static string GetApplicationName(Assembly callingAssembly)
        {
            string name = "";
            if (callingAssembly != null) //may be null if calling from WebService
            {
                AssemblyName assemblyname = callingAssembly.GetName();
                name = assemblyname.Name;
            }

            return name;
        }

        /// <summary>
        /// Retrieves the name of the calling assembly
        /// </summary>
        /// <returns>Name of the calling assembly</returns>
        public static string GetApplicationName()
        {
#if (Smartphone || PocketPC)
            return GetApplicationName(Assembly.GetCallingAssembly());
#else
            return GetApplicationName(Assembly.GetEntryAssembly());
#endif
        }


        /// <summary>
        /// Uses the Environment.OSVersion to retrieve an abbreviated label for the operating system
        /// </summary>
        /// <returns>Win95,Win98,WinMe,WinNT,Win2K, or WinXP</returns>
        public static string GetOperatingSystem()
        {
            string os;

            if (Environment.OSVersion.Platform.ToString().Equals("Win32Windows"))
            {
                if (Environment.OSVersion.Version.Minor == 0)
                    os = "Win95";
                else if (Environment.OSVersion.Version.Minor < 90)
                    os = "Win98";
                else os = "WinMe";
            }
            else if (Environment.OSVersion.Platform.ToString().Equals("Win32NT"))
            {
                if (Environment.OSVersion.Version.Major <= 4)
                    os = "WinNT";
                else if (Environment.OSVersion.Version.Major <= 5)
                {
                    if (Environment.OSVersion.Version.Minor == 1)
                        os = "WinXP";
                    else if (Environment.OSVersion.Version.Minor == 0)
                        os = "Win2K";
                    else os = "Win03";
                }
                else os = "WinVi";
            }
            else os = Environment.OSVersion.Platform.ToString();

            return os;

        }





        public static string GetApplicationDirectory()
        {
#if (Smartphone || PocketPC)		
            return Path.GetDirectoryName(System.Reflection.Assembly.GetCallingAssembly().GetName().CodeBase);        
#else
            return Path.GetDirectoryName(AppDomain.CurrentDomain.BaseDirectory);
#endif            
        }
        #endregion



        #region PUBLIC METHODS

        #region LOGGING
        #region LOG ERROR
        public static void LogError(Exception ex)
        {
            LogError(_defaultLogName, "", ex, "");
        }
        public static void LogError(string message)
        {
            LogError(_defaultLogName, "", message, "");
        }
        public static void LogError(string codeLocation, Exception ex)
        {
            LogError(_defaultLogName, codeLocation, ex, "");
        }
        public static void LogError(string codeLocation,string message)
        {
            LogError(_defaultLogName, codeLocation, message, "");
        }
        public static void LogError(string codeLocation, Exception ex, string notes)
        {
            LogError(_defaultLogName, codeLocation, ex, notes);
        }
        public static void LogError(string codeLocation, string logevent, string notes)
        {
            LogError(_defaultLogName, codeLocation, logevent, notes);
        }
        public static void LogError(string logName, string codeLocation, string logevent, string notes)
        {
            Log(logName, LogLevels.ERROR, codeLocation, logevent, notes);
        }
        public static void LogError(string logName, string codeLocation, Exception ex, string notes)
        {
            string message = ((ex != null) ? ex.ToString() : "");
            Log(logName, LogLevels.ERROR, codeLocation, message, notes);
        }
        #endregion

        #region LOG WARNING
        public static void LogWarning(string message)
        {
            LogWarning(_defaultLogName, "", message, "");
        }
        public static void LogWarning(string codeLocation, string message)
        {
            LogWarning(_defaultLogName, codeLocation, message, "");
        }
        public static void LogWarning(string codeLocation, string logevent, string notes)
        {
            LogWarning(_defaultLogName, codeLocation, logevent, notes);
        }
        public static void LogWarning(string logName, string codeLocation, string logevent, string notes)
        {
            Log(logName, LogLevels.WARNING, codeLocation, logevent, notes);
        }
        #endregion

        #region LOG INFO
        public static void LogInfo(string message)
        {
            LogInfo(_defaultLogName, "", message, "");
        }
        public static void LogInfo(string codeLocation, string message)
        {
             LogInfo(_defaultLogName, codeLocation, message, "");
        }
        public static void LogInfo(string codeLocation, string logevent, string notes)
        {
            LogInfo(_defaultLogName, codeLocation, logevent, notes);
        }
        public static void LogInfo(string logName, string codeLocation, string logevent, string notes)
        {
            Log(logName, LogLevels.INFO, codeLocation, logevent, notes);
        }
        #endregion

        #region LOG DEBUG
        public static void LogDebug(string message)
        {
            LogDebug(_defaultLogName, "", message, "");
        }
        public static void LogDebug(string codeLocation, string message)
        {
            LogDebug(_defaultLogName, codeLocation, message, "");
        }
        public static void LogDebug(string codeLocation, string logevent, string notes)
        {
            LogDebug(_defaultLogName, codeLocation, logevent, "");
        }
        public static void LogDebug(string logName, string codeLocation, string logevent, string notes)
        {
            Log(logName, LogLevels.DEBUG, codeLocation, logevent, notes);
        }
        #endregion

        public static void Log(string logname, LogLevels level, string codeLocation, string logevent, string notes)
        {            
            if (level >= _logLevel)
            {
                #region DETERMINE LOG FILE NAME
                string filename;
                if (_isLoggingByHour) filename = String.Format("{0}_{1}_{2}_{3}_{4}{5}", logname, DateTime.Now.Year, DateTime.Now.Month.ToString("00"), DateTime.Now.Day.ToString("00"), DateTime.Now.Hour.ToString("00"), _extension);
                else if (_isLoggingByDay) filename = String.Format("{0}_{1}_{2}_{3}{4}", logname, DateTime.Now.Year, DateTime.Now.Month.ToString("00"), DateTime.Now.Day.ToString("00"), _extension);
                else filename = logname + _extension;
                #endregion

                bool isError = level.Equals(LogLevels.ERROR);

                #region Prepare entry - remove newlines, commas, add date
                codeLocation = codeLocation.Replace(NEWLINE, ";").Replace(",", ";");
                logevent = logevent.Replace(NEWLINE, ";").Replace(",", ";");
                notes = notes.Replace(NEWLINE, ";").Replace(",", ";");

                string datetime = String.Format("{0}/{1}/{2} {3}:{4}:{5}", DateTime.Now.Month.ToString("00"), DateTime.Now.Day.ToString("00"), DateTime.Now.Year.ToString("00"), DateTime.Now.Hour.ToString("00"), DateTime.Now.Minute.ToString("00"), DateTime.Now.Second.ToString("00"));
                long tickCount = Environment.TickCount;
                long sinceTick = tickCount - _lastTick;
                _lastTick = tickCount;
                #endregion

                string logDirectory = LogDirectory();
                string filepath = Path.Combine(logDirectory, filename);

                try
                {
                    StringBuilder sbEntry = new StringBuilder();

                    bool isFirstTime = false;
                    if (!_isLoggingToBuffer && (!_pathCurrentLog.Equals(filepath) || (_sw == null))) isFirstTime = OpenLogFile(filepath);

                    #region header information if new file
                    if (isFirstTime && _isIncludingHeader && !_isLoggingToBuffer)
                    {
                        //application name; application version; machine name
                        sbEntry.Append(String.Format("{0} {1} {2} {3}", GetApplicationName(), GetApplicationVersion(), GetMachineName(), NEWLINE));
                        //screen width and height
                        sbEntry.Append(String.Format("screen width {0} x height {1}{2}", System.Windows.Forms.Screen.PrimaryScreen.Bounds.Width, System.Windows.Forms.Screen.PrimaryScreen.Bounds.Height, NEWLINE));
                        //OS version and name; .NET Framework version; culture language
                        sbEntry.Append(String.Format("{0};{1};.NET Framework {2};{3};{4}", Environment.OSVersion.ToString(), GetOperatingSystem(), Environment.Version.ToString(), CultureInfo.CurrentCulture.EnglishName, NEWLINE));
                        //culture date format; culture time format; local date; universal date
                        sbEntry.Append(String.Format("{0};{1};{2};{3};{4}", CultureInfo.CurrentCulture.DateTimeFormat.ShortDatePattern, CultureInfo.CurrentCulture.DateTimeFormat.ShortTimePattern, DateTime.Now, DateTime.UtcNow, NEWLINE));
                        sbEntry.Append(NEWLINE);
                        sbEntry.Append(",DateTime,Tick,Elapsed,Level,CodeLocation,LogEvent,Notes");
                        //if (_isIncludingSystemInfo)
                        //    sbEntry.Append(SystemStatus.StatusColumns);
                        sbEntry.Append(NEWLINE);
                    }
                    #endregion

                    #region ASSEMBLE LOG ENTRY
                    sbEntry.Append(String.Format(",{0},{1},{2},{3},{4},{5},{6}", datetime, tickCount, sinceTick, LevelLabel(level), codeLocation, logevent, notes));
                    //if (_isIncludingSystemInfo) sbEntry.Append(SystemStatus.GetStatusString());
                    #endregion

                    #region WRITE LOG ENTRY
                    lock (typeof(Logger))
                    {
                        string logEntry = sbEntry.ToString();
                        if (!_isLoggingToBuffer)
                        {
                            WriteToFile(logEntry, isError);
                        }
                        else
                        {
                            WriteToBuffer(logEntry);
                            if (isError && _writesBufferToFileOnError) WriteBufferToFile();
                        }

                        if (_isLoggingToConsole) Console.WriteLine(logEntry);
                    }
                    #endregion

                }
                catch {}


                #region IF LIMITING SIZE AND LOG EXCEEDS SIZE, RENAME
                if (!_isLoggingToBuffer && _isLimitingSize)
                {
                    FileInfo fi = new FileInfo(filepath);
                    if ((fi.Length / 1000) > _kbSizeLimit)
                    {
                        CloseLogFile();
                        string fileCopy = String.Format("{0}_{1}_{2}_{3}_{4}_{5}_{6}{7}", logname, DateTime.Now.Year, DateTime.Now.Month.ToString("00"), DateTime.Now.Day.ToString("00"), DateTime.Now.Hour.ToString("00"), DateTime.Now.Minute.ToString("00"), DateTime.Now.Second.ToString("00"), _extension);
                        try
                        {
                            File.Copy(filepath, Path.Combine(logDirectory, fileCopy), true);
                            File.Delete(filepath);
                        }
                        catch { }
                    }
                }
                #endregion

                #region DELETE OLD FILES
                if (_deletesOldLogs)
                {
                    try
                    {
                        string[] logs = Directory.GetFiles(logDirectory);
                        if (logs.Length > _keepLogCount)
                        {
                            Array.Sort(logs, new Utilities.CompareFileWriteTime());
                            for (int i = 0; i < (logs.Length - _keepLogCount); i++)
                            {
                                File.Delete(logs[0]);
                            }
                        }
                    }
                    catch { }
                }
                #endregion

            }

           
        }
        #endregion

        #region WRITE TO FILE
        public static void WriteBufferToFile() { WriteBufferToFile(_defaultLogName); }
        public static void WriteBufferToFile(string logFileName)
        {
            if ((_isLoggingToBuffer) && (_sb != null))
            {
                OpenLogFile(Path.Combine(LogDirectory(), logFileName));
                if (_sw != null) _sw.Write(_sb.ToString());
                _sb = null;
            }

            CloseLogFile();
        }
        #endregion

        public static void Close()
        {
            CloseLogFile();
        }

        #endregion

        #region PRIVATE METHODS
        private static string LevelLabel(LogLevels level)
        {
            string label = "";
            switch (level)
            {
                case LogLevels.ERROR: label = "ERROR"; break;
                case LogLevels.DEBUG: label = "DEBUG"; break;
                case LogLevels.INFO: label = "INFO"; break;
                case LogLevels.WARNING: label = "WARNING"; break;                
            }
            return label;
        }
        private static string LogDirectory()
        {
            if (_parentDirectory.Length == 0) _parentDirectory = GetApplicationDirectory(); 
            string path = _parentDirectory;

            if (_savesInLogsFolder) path = Path.Combine(_parentDirectory, "logs");
            
            if (!Directory.Exists(path)) Directory.CreateDirectory(path);
                        
            return path;
        }
        private static void WriteToFile(string logentry, bool isError)
        {
            if (_sw != null)
            {
                _sw.WriteLine(logentry);
                _countWrites++;

                #region FLUSH?
                if (isError || (_countWrites > _flushFrequency))
                {
                    CloseLogFile();
                }
                #endregion
            }
        }
        private static void WriteToBuffer(string logentry)
        {
            if (_sb == null) _sb = new StringBuilder();
            _sb.Append(logentry + NEWLINE);
        }
        private static bool OpenLogFile(string filepath)
        {
            bool isFirstTime = false;

            try
            {
                CloseLogFile();

                isFirstTime = !File.Exists(filepath);

                lock (typeof(Logger))
                {

                    _fs = new FileStream(filepath, FileMode.Append);
                    _sw = new StreamWriter(_fs);
                    _pathCurrentLog = filepath;
                    _countWrites = 0;
                }

            }
            catch { }

            return isFirstTime;

        }
        private static void CloseLogFile()
        {
            if (_sw != null)
            {
                try
                {
                    _sw.Flush();
                }
                finally
                {
                    _pathCurrentLog = "";
                    if (_sw != null)
                    {
                        _sw.Close();
                        _sw = null;
                    }
                    if (_fs != null)
                    {
                        _fs.Close();
                        _fs = null;
                    }
                }

            }
        }
        #endregion
    }
}
