// 32feet.NET - Personal Area Networking for .NET
//
// Copyright (c) 2003-2007 In The Hand Ltd, All rights reserved.
// This source code is licensed under the In The Hand Community License - see License.txt

namespace InTheHand.Net.Bluetooth
{

#if WinCE

    // Used by InTheHand.Net.Sockets.BluetoothDeviceInfo.GetServiceRecordsUnparsed(System.Guid)
    // Moved from /BTHNS_RESTRICTIONBLOB.cs.
    internal enum SdpQueryType : int
    {
        SearchRequest = 1,
        AttributeRequest = 2,
        SearchAttributeRequest = 3,
    }//enum

#endif

}