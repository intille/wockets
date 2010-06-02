using Wockets.Data.Configuration;
using Wockets.Exceptions;

namespace Wockets
{
    /// <summary>
    /// The class includes global instances of key and active wockets objects including the wockets controller, the wockets
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
        public static WocketsConfiguration _Configuration;

        /// <summary>
        /// The version number of the wockets software
        /// </summary>
        public static string _Version="1.39";

        /// <summary>
        /// The date the software was last modified
        /// </summary>
        public static string _Date ="June 2nd, 2010";

        /// <summary>
        /// Specifies the last error code reported
        /// </summary>
        public static ErrorCodes _LastError = ErrorCodes.NONE;

        public static string _LastErrorMessage = "";

    }
}
