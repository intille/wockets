// 32feet.NET - Personal Area Networking for .NET
//
// InTheHand.Net.Bluetooth.BLUETOOTH_RADIO_INFO
// 
// Copyright (c) 2003-2006 In The Hand Ltd, All rights reserved.
// This source code is licensed under the In The Hand Community License - see License.txt

using System;
using System.Runtime.InteropServices;

namespace InTheHand.Net.Bluetooth
{
#if WinXP
    [StructLayout(LayoutKind.Sequential, CharSet=CharSet.Unicode)]
#endif
    internal struct BLUETOOTH_RADIO_INFO
    {
        internal int dwSize;
        internal long address;
#if WinXP
        [MarshalAs(UnmanagedType.ByValTStr, SizeConst=248)]
#endif
        internal string szName; //[BLUETOOTH_MAX_NAME_SIZE];
        internal uint ulClassofDevice;
        internal ushort lmpSubversion;
#if WinXP
        [MarshalAs(UnmanagedType.U2)]
#endif
        internal Manufacturer manufacturer;
    }
}
