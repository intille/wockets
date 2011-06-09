using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets
{

    /// <summary>
    /// Types of memory modes supported by the wockets
    /// </summary>
    public enum MemoryMode
    {
        /// <summary>
        /// Data written directly from the bluetooth stream to a local memory buffer within the applications address space
        /// </summary>
        BluetoothToLocal,

        /// <summary>
        /// Data written from the bluetooth stream to a shared memory mapped file
        /// </summary>
        BluetoothToShared,

        /// <summary>
        /// Data written from the shared memory mapped file to a local memory buffer within the applications address space
        /// </summary>
        SharedToLocal
    }
}
