using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Kernel.Types
{
    /// <summary>
    /// Specifies types of memory mode supported by the kernel
    /// </summary>
    public enum MemoryMode
    {

        /// <summary>
        /// Data is written to shared memory mapped files not within the application's address space, most communication is event based
        /// </summary>
        Shared,

        /// <summary>
        /// Data is written to memory buffers within the applications address space
        /// </summary>
        Nonshared
    }
}
