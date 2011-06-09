using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Exceptions
{
    public enum ErrorCodes
    {
        /// <summary>
        /// Wocket failed to send data on the uplink
        /// </summary>
        SOCKET_SEND_FAILED, 

        /// <summary>
        /// Creating the endpoint bluetooth address failed
        /// </summary>
        REMOTE_ENDPOINT_CREATION_FAILED,

        /// <summary>
        /// A wocket connections stream timedout
        /// </summary>
        CONNECTION_TIMEOUT,

        /// <summary>
        /// A wocket connection stream failed
        /// </summary>
        CONNECTION_FAILED,

        /// <summary>
        /// A wocket bluetooth stream did not close properly
        /// </summary>
        CONNECTION_FAILED_TO_CLOSE,

        /// <summary>
        /// A wocket bluetooth stream did not open properly
        /// </summary>
       CONNECTION_FAILED_TO_OPEN,

        /// <summary>
        /// No error
        /// </summary>
        NONE
    }
}
