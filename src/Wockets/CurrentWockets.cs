using System;
using Wockets.Data.Configuration;
using Wockets.Exceptions;
using System.Reflection;


namespace Wockets
{
    
    /// <summary>
    /// This singleton class includes global instances of key and active wockets objects including the wockets controller, the wockets
    /// configuration, version and date information
    /// </summary>
    public class CurrentWockets
    {
        /// <summary>
        /// A reference to the currently active wockets controller
        /// </summary>
        public static WocketsController _Controller;

        /// <summary>
        /// A reference to the current wockets configuration that is used
        /// </summary>
        public static WocketsConfiguration _Configuration=null;

        //public static bool _Continuous = false;

        /// <summary>
        /// The version number of the wockets software
        /// </summary>
        public static string _Version
        {
            get
            {                
                Assembly assembly = Assembly.GetCallingAssembly(); 
                AssemblyName assemblyName = assembly.GetName();
                return assemblyName.Version.ToString();
            }
        }

        /// <summary>
        /// The date the software was last modified
        /// </summary>
        public static string _Date ="August 21st, 2010";

        /// <summary>
        /// Specifies the last error code reported
        /// </summary>
        public static ErrorCodes _LastError = ErrorCodes.NONE;

        public static string _LastErrorMessage = "";

    }
}
