using System;
using System.IO;
using System.Runtime.InteropServices;

using System.Reflection; //for version
using System.Globalization;
using System.Diagnostics; //for culture info




	/// <summary>
	/// Summary description for Logger.
	/// </summary>
	public class Logger
	{

        public static string NEWLINE  = Microsoft.VisualBasic.ControlChars.NewLine;


		private static string _pathLogDirectory =  "";
        private static string _defaultLogName = "log";
				
		private static bool _isLoggingDebug = true;
        
		private static bool _isLoggingToConsole = false;

        private static int _kbLimit = 100;
        private static int _countCheckSize = 0;
        private static long _lastTick = 0;
                

        #region PROPERTIES
        /// <summary>
        /// Absolute path where log files are saved
        /// </summary>
        public static string LogDirectory
        {
            get { return _pathLogDirectory; }
            set { _pathLogDirectory = value; if (!Directory.Exists(_pathLogDirectory)) Directory.CreateDirectory(_pathLogDirectory); }
        }
        public static string DefaultPath
        {
            get { return Path.Combine(_pathLogDirectory,_defaultLogName + ".txt"); }
        }

        /// <summary>
        /// Maximum size of file in kilobytes; when it reaches this size, logger will delete and start new file
        /// </summary>
        public static int LogFileKBLimit
        {
            get { return _kbLimit; }
            set { _kbLimit = value; }
        }

        /// <summary>
        /// Whether to log entries with the category "debug"
        /// </summary>
        public static bool IsLoggingDebug
        {
            get { return _isLoggingDebug; }
            set { _isLoggingDebug = value; }
        }

        /// <summary>
        /// Whether to also log to console
        /// </summary>
        public static bool IsLoggingToConsole
        {
            get { return _isLoggingToConsole; }
            set { _isLoggingToConsole = false; }
        }
        #endregion

		#region GET APPLICATION ATTRIBUTES
		/// <summary>
		/// Retrieves the version of the calling assembly, which is set in the AssemblyInfo.cs file
		/// This method allows you to send a specific assembly (usually retrieved with Assembly.GetCallingAssembly())
		/// </summary>
		/// <returns>String version of calling assembly</returns>
		public static string GetAppVersion()
		{
            AssemblyName assemblyname = Assembly.GetCallingAssembly().GetName();
			Version assemblyver = assemblyname.Version;
			return assemblyver.ToString();
		}

		/// <summary>
		/// Retrieves the name of the calling assembly
		/// </summary>
		/// <returns>Name of the calling assembly</returns>
		public static string GetAppName()
		{

            AssemblyName assemblyname = Assembly.GetCallingAssembly().GetName();
			
			return assemblyname.Name;
		}
        /// <summary>
        /// Retrieves the path of the folder containing the calling assembly
        /// </summary>
        /// <returns>Path of the calling assembly</returns>
        public static string GetAppDirectory()
        {
            return Path.GetDirectoryName(System.Reflection.Assembly.GetCallingAssembly().GetName().CodeBase);               
        }

		#endregion
		
		#region LOGGING
        /// <summary>
        /// Log to general application log ("application prefix") as category "error"
        /// </summary>
        /// <param name="context">Method name or simple context description</param>
        /// <param name="problem">Error text</param>
        public static void LogError(string context, string problem) { Log(_defaultLogName, context, "error", problem, ""); }
        /// <summary>
        /// Log to general application log ("application prefix") as category "error"
        /// </summary>
        /// <param name="context">Method name or simple context description</param>
        /// <param name="problem">Error text</param>
        /// <param name="extrainfo">Helpful information</param>
        public static void LogError(string context, string problem, string extrainfo) { Log(_defaultLogName, context, "error", problem, extrainfo); }
        /// <summary>
        /// Log to general application log ("application prefix") as category "debug"
        /// </summary>
        /// <param name="context">Method name or simple context description</param>
        /// <param name="note">Note text</param>
        public static void LogDebug(string context, string note) { Log(_defaultLogName, context, "debug", note, ""); }


		/// <summary>
		/// Log to specific application log,  {logname}.csv;
		/// </summary>
		/// <param name="logname">Prefix for specific log file</param>
		/// <param name="subject">Method or ID of object/entry/information to which action pertains</param>
		/// <param name="category">Type of logentry: debug, error, server, etc.</param>
		/// <param name="action">Event or action taken</param>
		/// <param name="notes">Extra notes about event or action</param>
		public static void Log(string logname, string subject, string category,string action,string notes)
		{
            if (_pathLogDirectory.Length == 0)
            {
                LogDirectory = Path.Combine(Path.GetDirectoryName(System.Reflection.Assembly.GetCallingAssembly().GetName().CodeBase), "logs");
            }

            if (!category.ToLower().Equals("debug") || _isLoggingDebug)
            {
                FileStream fs = null;
                StreamWriter sw = null;

                string filename = logname + ".txt";

                #region Prepare entry - remove newlines, commas, add date
                action = action.Replace(NEWLINE, ";").Replace(",", ";");
                notes = notes.Replace(NEWLINE, ";").Replace(",", ";");
                long tickDiff = (_lastTick > 0) ? Environment.TickCount - _lastTick : 0;
                _lastTick = Environment.TickCount;
                string datetime = String.Format("{0}/{1}/{2} {3}:{4}:{5}", DateTime.Now.Month, DateTime.Now.Day, DateTime.Now.Year, DateTime.Now.Hour, DateTime.Now.Minute, DateTime.Now.Second);
                string logentry = String.Format("{0},{1},{2},{3},{4},{5}", datetime, tickDiff, category, subject, action, notes);
                #endregion

                string filepath = Path.Combine(_pathLogDirectory, filename);

                #region CHECK IF LOG IS TOO BIG
                if ((_countCheckSize % 10) == 0)
                {
                    try
                    {
                        FileInfo fi = new FileInfo(filepath);
                        if (fi.Length > _kbLimit * 1000) File.Delete(filepath);
                    }
                    catch { }
                }
                #endregion


                try
                {                    

                    bool firsttime = !File.Exists(filepath);


                    lock (typeof(Logger))
                    {

                        fs = new FileStream(filepath, FileMode.Append);
                        sw = new StreamWriter(fs);

                        #region header information if new file
                        if (firsttime)
                        {
                            sw.WriteLine(String.Format("{0} {1}", GetAppName(), GetAppVersion()));
                            sw.WriteLine(String.Format("{0},{1},{2},{3},{4},{5},{6},{7}", System.Windows.Forms.Screen.PrimaryScreen.Bounds.Width, System.Windows.Forms.Screen.PrimaryScreen.Bounds.Height, Environment.OSVersion.ToString(), CultureInfo.CurrentCulture.EnglishName, CultureInfo.CurrentCulture.DateTimeFormat.ShortDatePattern, CultureInfo.CurrentCulture.DateTimeFormat.ShortTimePattern, DateTime.Now, DateTime.UtcNow));
                            sw.WriteLine(".NET Framework " + Environment.Version.ToString());
                            sw.WriteLine();

                            sw.WriteLine("DateTime,Tick Diff,Category,Subject,Action,Result");

                        }
                        #endregion

                        sw.WriteLine(logentry);
                        sw.Close();
                        fs.Close();
                    }

                    if (_isLoggingToConsole) Console.WriteLine(logentry);

                }
                catch { }
                finally
                {
                    if (sw != null) sw.Close();
                    if (fs != null) fs.Close();
                }

                


            }
            

		}

		

    	#endregion

        public static string MakeCopy()
        { 
            return MakeCopy(_defaultLogName + "_copy.txt");
        }
        public static string MakeCopy(string filename)
        {
            string pathLog = Path.Combine(_pathLogDirectory, _defaultLogName + ".txt");
            string pathCopy = Path.Combine(_pathLogDirectory,filename);
            try
            {
                if (File.Exists(pathLog))
                    File.Copy(pathLog, pathCopy,true);
            }
            catch { }
            return pathCopy;
        }
    }

