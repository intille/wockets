// 32feet.NET - Personal Area Networking for .NET
//
// InTheHand.Net.Bluetooth.BLUETOOTH_DEVICE_INFO
// 
// Copyright (c) 2003-2008 In The Hand Ltd, All rights reserved.
// This source code is licensed under the In The Hand Community License - see License.txt

using System;
using System.Runtime.InteropServices;
#if WinXP
using InTheHand.Win32;
#endif

namespace InTheHand.Net.Bluetooth
{

#if WinXP
    [StructLayout(LayoutKind.Sequential, CharSet=CharSet.Unicode)]
#endif
    internal struct BLUETOOTH_DEVICE_INFO
    {
        internal int dwSize;
        internal long Address;
        internal uint ulClassofDevice;
#if WinXP
        [MarshalAs(UnmanagedType.Bool)]
#endif
        internal bool fConnected;
#if WinXP
        [MarshalAs(UnmanagedType.Bool)]
#endif
        internal bool fRemembered;
#if WinXP
        [MarshalAs(UnmanagedType.Bool)]
#endif
        internal bool fAuthenticated;
#if WinXP
        internal SYSTEMTIME stLastSeen;
        //[MarshalAs(UnmanagedType.ByValArray, SizeConst = 16, ArraySubType = UnmanagedType.U1)]
        internal SYSTEMTIME stLastUsed;  
        [MarshalAs(UnmanagedType.ByValTStr, SizeConst=248)]
#endif
        internal string szName;

        public BLUETOOTH_DEVICE_INFO(long address)
        {
            dwSize = 560;
            this.Address = address;
            ulClassofDevice = 0;
            fConnected = false;
            fRemembered = false;
            fAuthenticated = false;
#if WinXP
            stLastSeen = new SYSTEMTIME();
            stLastUsed = new SYSTEMTIME();

            // The size is much smaller on CE (no times and string not inline) it
            // appears to ignore the bad dwSize value.  So don't check this on CF.
            System.Diagnostics.Debug.Assert(Marshal.SizeOf(typeof(BLUETOOTH_DEVICE_INFO)) == dwSize, "BLUETOOTH_DEVICE_INFO SizeOf == dwSize");
#endif
            szName = "";
        }

        public BLUETOOTH_DEVICE_INFO(BluetoothAddress address)
        {
            if (address == null) {
                throw new ArgumentNullException("address");
            }
            dwSize = 560;
            this.Address = address.ToInt64();
            ulClassofDevice = 0;
            fConnected = false;
            fRemembered = false;
            fAuthenticated = false;
#if WinXP
            stLastSeen = new SYSTEMTIME();
            stLastUsed = new SYSTEMTIME();

            // The size is much smaller on CE (no times and string not inline) it
            // appears to ignore the bad dwSize value.  So don't check this on CF.
            System.Diagnostics.Debug.Assert(Marshal.SizeOf(typeof(BLUETOOTH_DEVICE_INFO)) == dwSize, "BLUETOOTH_DEVICE_INFO SizeOf == dwSize");
#endif
            szName = "";
        }

#if WinXP
        internal DateTime LastSeen
        {
            get
            {
                return stLastSeen.ToDateTime();
            }
        }
        internal DateTime LastUsed
        {
            get
            {
                return stLastUsed.ToDateTime();
            }
        }
#endif
    }
}
