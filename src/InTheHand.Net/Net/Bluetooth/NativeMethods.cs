// 32feet.NET - Personal Area Networking for .NET
//
// InTheHand.Net.Bluetooth.NativeMethods
// 
// Copyright (c) 2003-2008 In The Hand Ltd, All rights reserved.
// This source code is licensed under the In The Hand Community License - see License.txt

using System;
using System.Runtime.InteropServices;

namespace InTheHand.Net.Bluetooth
{
#if V2
    internal static class NativeMethods
    {
#else
	internal class NativeMethods
	{
        private NativeMethods(){}
#endif

#if WinCE
        private const string wsDll = "ws2.dll";
        internal const string ceRegistryRoot = "\\SOFTWARE\\Microsoft\\Bluetooth\\";
#else
        private const string wsDll = "ws2_32.dll";
#endif

#if WinCE
		//CE 5.0
		[DllImport("btdrt.dll", SetLastError=true)]
		public static extern int BthAcceptSCOConnections(int fAccept);

		[DllImport("btdrt.dll", SetLastError=true)]
        public static extern int BthAuthenticate(byte[] pbt);

		[DllImport("btdrt.dll", SetLastError=true)]
		public static extern int BthCancelInquiry();

		[DllImport("btdrt.dll", SetLastError=true)]
		public static extern int BthClearInquiryFilter();

		[DllImport("btdrt.dll", SetLastError=true)]
		public static extern int BthCloseConnection(ushort handle);

		[DllImport("btdrt.dll", SetLastError=true)]
        public static extern int BthCreateACLConnection(byte[] pbt, out ushort phandle);

		[DllImport("btdrt.dll", SetLastError=true)]
        public static extern int BthCreateSCOConnection(byte[] pbt, out ushort phandle);
        /*
		[DllImport("btdrt.dll", SetLastError=true)]
        public static extern int BthEnterHoldMode(ref long pba, ushort hold_mode_max, ushort hold_mode_min, ref ushort pinterval);

		[DllImport("btdrt.dll", SetLastError=true)]
        public static extern int BthEnterParkMode(ref long pba, ushort beacon_max, ushort beacon_min, ref ushort pinterval);

		[DllImport("btdrt.dll", SetLastError=true)]
        public static extern int BthEnterSniffMode(ref long pba, ushort sniff_mode_max, ushort sniff_mode_min, ushort sniff_attempt, ushort sniff_timeout, ref ushort pinterval);

		[DllImport("btdrt.dll", SetLastError=true)]
        public static extern int BthExitParkMode(ref long pba);

		[DllImport("btdrt.dll", SetLastError=true)]
        public static extern int BthExitSniffMode(ref long pba);
        */


        [DllImport("btdrt.dll", SetLastError = true)]
        public static extern int BthEnterHoldMode(ref long pba, ushort hold_mode_max, ushort hold_mode_min, ref ushort pinterval);

        [DllImport("btdrt.dll", SetLastError = true)]
        public static extern int BthEnterParkMode(ref long pba, ushort beacon_max, ushort beacon_min, ref ushort pinterval);

        [DllImport("btdrt.dll", SetLastError = true)]
        public static extern int BthEnterSniffMode(byte[] pba, ushort sniff_mode_max, ushort sniff_mode_min, ushort sniff_attempt, ushort sniff_timeout, ref ushort pinterval);

        [DllImport("btdrt.dll", SetLastError = true)]
        public static extern int BthExitParkMode(ref long pba);

        [DllImport("btdrt.dll", SetLastError = true)]
        public static extern int BthExitSniffMode(byte[] pba);



        [DllImport("btdrt.dll", SetLastError=true)]
		public static extern int BthGetAddress(ushort handle, out long pba);

		[DllImport("btdrt.dll", SetLastError=true)]
		public static extern int BthGetBasebandConnections(int cConnections, byte[] pConnections, ref int pcConnectionsReturned);

		[DllImport("btdrt.dll", SetLastError=true)]
		public static extern int BthGetBasebandHandles(int cHandles, ref ushort pHandles, ref int pcHandlesReturned);

		[DllImport("btdrt.dll", SetLastError=true)]
        public static extern int BthGetCurrentMode(byte[] pba, ref byte pmode);

		[DllImport("btdrt.dll", SetLastError=true)]
		public static extern int BthGetHardwareStatus(ref HardwareStatus pistatus);

		[DllImport("btdrt.dll", SetLastError=true)]
        public static extern int BthGetLinkKey(byte[] pba, ref Guid key);

		[DllImport("btdrt.dll", SetLastError=true)]
        public static extern int BthGetPINRequest(byte[] pba);

		[DllImport("btdrt.dll", SetLastError=true)]
        public static extern int BthGetRemoteCOD(byte[] pbt, out uint pcod);

		//CE 5.0
		[DllImport("btdrt.dll", SetLastError=true)]
        public static extern int BthPairRequest(byte[] pba, int cPinLength, byte[] ppin);

		[DllImport("btdrt.dll", SetLastError=true)]
		public static extern int BthPerformInquiry(int LAP, byte length, byte num_responses,
			int cBuffer, ref int pcDiscoveredDevices, byte[] InquiryList);

		[DllImport("btdrt.dll", SetLastError=true)]
		public static extern int BthReadAuthenticationEnable(out byte pae);

		[DllImport("btdrt.dll", SetLastError=true)]
		public static extern int BthReadCOD(out uint pcod);

		[DllImport("btdrt.dll", SetLastError=true)]
        public static extern int BthReadLinkPolicySettings(byte[] pba, ref ushort plps);

		[DllImport("btdrt.dll", SetLastError=true)]
        public static extern int BthReadLocalAddr(byte[] pba);

		[DllImport("btdrt.dll", SetLastError=true)]
		public static extern int BthReadLocalVersion(out byte phci_version, out ushort phci_revision,
			out byte plmp_version, out ushort plmp_subversion, out ushort pmanufacturer, out byte plmp_features);

		[DllImport("btdrt.dll", SetLastError=true)]
		public static extern int BthReadPageTimeout(out ushort ptimeout);

		[DllImport("btdrt.dll", SetLastError=true)]
        public static extern int BthReadRemoteVersion(byte[] pba, ref byte plmp_version,
			ref ushort plmp_subversion, ref ushort pmanufacturer, ref byte plmp_features);

		[DllImport("btdrt.dll", SetLastError=true)]
		public static extern int BthReadScanEnableMask(out byte pmask);

        //CE 6.0
        [DllImport("btdrt.dll", SetLastError = true)]
        public static extern int BthReadRSSI(byte[] pbt, out sbyte pbRSSI);

		[DllImport("btdrt.dll", SetLastError=true)]
        public static extern int BthRefusePINRequest(byte[] pbt);

		[DllImport("btdrt.dll", SetLastError=true)]
        public static extern int BthRemoteNameQuery(byte[] pba, int cBuffer, out int pcRequired, byte[] szString);

		[DllImport("btdrt.dll", SetLastError=true)]
        public static extern int BthRevokeLinkKey(byte[] pba);

		[DllImport("btdrt.dll", SetLastError=true)]
        public static extern int BthRevokePIN(byte[] pba);

		[DllImport("btdrt.dll", SetLastError=true)]
        public static extern int BthSetEncryption(byte[] pba, int fOn);

		[DllImport("btdrt.dll", SetLastError=true)]
        public static extern int BthSetInquiryFilter(byte[] pba);

		[DllImport("btdrt.dll", SetLastError=true)]
        public static extern int BthSetLinkKey(byte[] pba, ref Guid key);

		[DllImport("btdrt.dll", SetLastError=true)]
        public static extern int BthSetPIN(byte[] pba, int cPinLength, byte[] ppin);

		[DllImport("btdrt.dll", SetLastError=true)]
		public static extern int BthSetSecurityUI(IntPtr hEvent, int dwStoreTimeout, int dwProcTimeout);
		
		[DllImport("btdrt.dll", SetLastError=true)]
		public static extern int BthTerminateIdleConnections();

		[DllImport("btdrt.dll", SetLastError=true)]
		public static extern int BthWriteAuthenticationEnable(byte ae);

		[DllImport("btdrt.dll", SetLastError=true)]
		public static extern int BthWriteCOD(uint cod);

		[DllImport("btdrt.dll", SetLastError=true)]
        public static extern int BthWriteLinkPolicySettings(byte[] pba, ushort lps);

		[DllImport("btdrt.dll", SetLastError=true)]
		public static extern int BthWritePageTimeout(ushort timeout);
		
		[DllImport("btdrt.dll", SetLastError=true)]
		public static extern int BthWriteScanEnableMask(byte mask);



		//Utils
		[DllImport("BthUtil.dll", SetLastError=true)]
		public static extern int BthSetMode(RadioMode dwMode);

		[DllImport("BthUtil.dll", SetLastError=true)]
		public static extern int BthGetMode(out RadioMode dwMode);

        //msgqueue (for notifications)
        /*
        [DllImport("coredll.dll", SetLastError = true)]
        internal static extern IntPtr RequestBluetoothNotifications(BTE_CLASS dwClass, IntPtr hMsgQ);
        [DllImport("coredll.dll", SetLastError = true)]
        [return: MarshalAs(UnmanagedType.Bool)]
        internal static extern bool StopBluetoothNotifications(IntPtr h);

        internal enum BTE
        {
            CONNECTION = 100, 
            DISCONNECTION = 101, 
            ROLE_SWITCH = 102, 
            MODE_CHANGE = 103, 
            PAGE_TIMEOUT = 104, 
 
            KEY_NOTIFY = 200, 
            KEY_REVOKED = 201, 
 
            LOCAL_NAME = 300, 
            COD = 301, 
 
            STACK_UP = 400, 
            STACK_DOWN = 401, 
        }

        [Flags()]
        internal enum BTE_CLASS
        {
            CONNECTIONS = 1,
            PAIRING = 2, 
            DEVICE = 4,
            STACK = 8,
        }

        [DllImport("coredll.dll", SetLastError = true)]
        [return: MarshalAs(UnmanagedType.Bool)]
        internal static extern bool CloseMsgQueue(IntPtr hMsgQ);

        [DllImport("coredll.dll", SetLastError = true)]
        internal static extern IntPtr CreateMsgQueue(string lpszName, ref MSGQUEUEOPTIONS lpOptions);

        [DllImport("coredll.dll", SetLastError = true)]
        [return: MarshalAs(UnmanagedType.Bool)]
        internal static extern bool ReadMsgQueue(IntPtr hMsgQ, IntPtr lpBuffer, int cbBufferSize, out int lpNumberOfBytesRead, int dwTimeout, out int pdwFlags);

        [StructLayout(LayoutKind.Sequential)]
        internal struct MSGQUEUEOPTIONS
        {
            internal int dwSize;
            internal int dwFlags;
            internal int dwMaxMessages;
            internal int cbMaxMessage;
            [MarshalAs(UnmanagedType.Bool)]
            internal bool bReadAccess;
        }

        [StructLayout(LayoutKind.Sequential)]
        internal struct BTEVENT
        {
            internal BTE dwEventId;
            internal int dwReserved;
            [MarshalAs(UnmanagedType.ByValArray, SizeConst=64)]
            internal byte[] baEventData;
        }

        internal struct BT_CONNECT_EVENT
        {
            internal int dwSize;
            internal ushort hConnection;
            internal long bta;
            internal byte ucLinkType;
            internal byte ucEncryptMode;
        }
        */

#if V1
		[DllImport("coredll.dll", SetLastError=true)]
		public static extern int LocalFree(IntPtr ptr);
#endif

#endif

        //SetService
        [DllImport(wsDll, EntryPoint = "WSASetService", SetLastError = true)]
        public static extern int WSASetService(ref InTheHand.Net.Sockets.WSAQUERYSET lpqsRegInfo, WSAESETSERVICEOP essoperation, int dwControlFlags);

        //LookupService
        [DllImport(wsDll, EntryPoint = "WSALookupServiceBegin", SetLastError = true)]
        public static extern int WSALookupServiceBegin(byte[] pQuerySet, LookupFlags dwFlags, out int lphLookup);

        [DllImport(wsDll, EntryPoint = "WSALookupServiceBegin", SetLastError = true)]
        public static extern int WSALookupServiceBegin(ref InTheHand.Net.Sockets.WSAQUERYSET pQuerySet, LookupFlags dwFlags, out int lphLookup);

		[DllImport(wsDll, EntryPoint="WSALookupServiceNext", SetLastError=true)]
		public static extern int WSALookupServiceNext(int hLookup, LookupFlags dwFlags, ref int lpdwBufferLength, byte[] pResults);

		[DllImport(wsDll, EntryPoint="WSALookupServiceEnd", SetLastError=true)]
        public static extern int WSALookupServiceEnd(int hLookup);


        
        

#if WinXP

        [DllImport("user32.dll", SetLastError=true, CharSet=CharSet.Unicode)]
        internal static extern int RegisterDeviceNotification(IntPtr hRecipient, ref DEV_BROADCAST_HANDLE NotificationFilter, int Flags);

        [StructLayout(LayoutKind.Sequential)]
        internal struct DEV_BROADCAST_HDR
        {
            internal int dbch_size;
            internal int dbch_devicetype;
            private int dbch_reserved;
        }

        [StructLayout(LayoutKind.Sequential)]
        internal struct DEV_BROADCAST_HANDLE
        {
            internal int dbch_size;
            internal int dbch_devicetype;
            private int dbch_reserved;
            internal IntPtr dbch_handle;
            internal IntPtr dbch_hdevnotify;
            internal Guid dbch_eventguid;
            internal int dbch_nameoffset;
            internal byte dbch_data;

        }

        internal const int DBT_DEVTYP_HANDLE = 0x00000006;
        internal const int WM_DEVICECHANGE = 0x0219;

        // {0850302A-B344-4fda-9BE9-90576B8D46F0}
        internal static readonly Guid GUID_BTHPORT_DEVICE_INTERFACE = new Guid(0x850302a, 0xb344, 0x4fda, 0x9b, 0xe9, 0x90, 0x57, 0x6b, 0x8d, 0x46, 0xf0);

// {EA3B5B82-26EE-450E-B0D8-D26FE30A3869}
        internal static readonly Guid GUID_BLUETOOTH_RADIO_IN_RANGE = new Guid(0xea3b5b82, 0x26ee, 0x450e, 0xb0, 0xd8, 0xd2, 0x6f, 0xe3, 0x0a, 0x38, 0x69);

// {E28867C9-C2AA-4CED-B969-4570866037C4}
        internal static readonly Guid GUID_BLUETOOTH_RADIO_OUT_OF_RANGE = new Guid(0xe28867c9, 0xc2aa, 0x4ced, 0xb9, 0x69, 0x45, 0x70, 0x86, 0x60, 0x37, 0xc4);

// BD198B7C-24AB-4B9A-8C0D-A8EA8349AA16
        internal static readonly Guid GUID_BLUETOOTH_PIN_REQUEST = new Guid(0xbd198b7c, 0x24ab, 0x4b9a, 0x8c, 0x0d, 0xa8, 0xea, 0x83, 0x49, 0xaa, 0x16);

// {7EAE4030-B709-4AA8-AC55-E953829C9DAA}
        internal static readonly Guid GUID_BLUETOOTH_L2CAP_EVENT = new Guid(0x7eae4030, 0xb709, 0x4aa8, 0xac, 0x55, 0xe9, 0x53, 0x82, 0x9c, 0x9d, 0xaa);

// {FC240062-1541-49BE-B463-84C4DCD7BF7F}
        internal static readonly Guid GUID_BLUETOOTH_HCI_EVENT = new Guid(0xfc240062, 0x1541, 0x49be, 0xb4, 0x63, 0x84, 0xc4, 0xdc, 0xd7, 0xbf, 0x7f);

        internal class BluetoothMessageFilter : System.Windows.Forms.IMessageFilter
        {
            #region IMessageFilter Members

            public bool PreFilterMessage(ref System.Windows.Forms.Message m)
            {
                if (m.Msg == WM_DEVICECHANGE)
                {
                    DEV_BROADCAST_HANDLE dbh = (DEV_BROADCAST_HANDLE)Marshal.PtrToStructure(m.LParam, typeof(DEV_BROADCAST_HANDLE));
                    return true;
                }

                return false;
            }

            #endregion
        }


        //[DllImport(wsDll, EntryPoint = "WSAAddressToString", SetLastError = true)]
        //public static extern int WSAAddressToString(byte[] lpsaAddress, int dwAddressLength, IntPtr lpProtocolInfo, System.Text.StringBuilder lpszAddressString, ref int lpdwAddressStringLength);
        
		//desktop methods
		[DllImport("Irprops.cpl", SetLastError=true, CharSet=CharSet.Unicode)]
        public static extern int BluetoothAuthenticateDevice(IntPtr hwndParent, IntPtr hRadio, ref BLUETOOTH_DEVICE_INFO pbtdi, string pszPasskey, int ulPasskeyLength);

		[DllImport("Irprops.cpl", SetLastError=true)]
        public static extern bool BluetoothDisplayDeviceProperties(IntPtr hwndParent, ref BLUETOOTH_DEVICE_INFO pbtdi);

		[DllImport("Irprops.cpl", SetLastError=true)]
		public static extern bool BluetoothEnableDiscovery(IntPtr hRadio, bool fEnabled);

		[DllImport("Irprops.cpl", SetLastError=true)]
		public static extern bool BluetoothEnableIncomingConnections(IntPtr hRadio, bool fEnabled);

		[DllImport("Irprops.cpl", SetLastError=true)]
        public static extern int BluetoothEnumerateInstalledServices(IntPtr hRadio, ref BLUETOOTH_DEVICE_INFO  pbtdi, ref int pcServices, byte[] pGuidServices);

        [DllImport("Irprops.cpl", SetLastError = true)]
        public static extern int BluetoothSetServiceState(IntPtr hRadio, ref BLUETOOTH_DEVICE_INFO pbtdi, ref Guid pGuidService, int dwServiceFlags);

		[DllImport("Irprops.cpl", SetLastError=true)]
		public static extern IntPtr BluetoothFindFirstRadio(ref BLUETOOTH_FIND_RADIO_PARAMS pbtfrp, ref IntPtr phRadio);

		[DllImport("Irprops.cpl", SetLastError=true)]
		public static extern bool BluetoothFindNextRadio(IntPtr hFind, ref IntPtr phRadio);

		[DllImport("Irprops.cpl", SetLastError=true)]
		public static extern bool BluetoothFindRadioClose(IntPtr hFind);


		[DllImport("Irprops.cpl", SetLastError=true)]
        public static extern int BluetoothGetDeviceInfo(IntPtr hRadio, ref BLUETOOTH_DEVICE_INFO pbtdi);

		[DllImport("Irprops.cpl", SetLastError=true)]
        public static extern int BluetoothGetRadioInfo(IntPtr hRadio, ref BLUETOOTH_RADIO_INFO pRadioInfo);


		[DllImport("Irprops.cpl", SetLastError=true)]
        public static extern bool BluetoothIsConnectable(IntPtr hRadio);

		[DllImport("Irprops.cpl", SetLastError=true)]
		public static extern bool BluetoothIsDiscoverable(IntPtr hRadio);

        [DllImport("Irprops.cpl", SetLastError=true)]
        public static extern int BluetoothUpdateDeviceRecord(ref BLUETOOTH_DEVICE_INFO pbtdi);


        //XP SDP Parsing
        [DllImport("Irprops.cpl", SetLastError = true)]
        public static extern int BluetoothSdpGetAttributeValue(byte[] pRecordStream, int cbRecordLength, ushort usAttributeId, IntPtr pAttributeData);

        [DllImport("Irprops.cpl", SetLastError = true)]
        public static extern int BluetoothSdpGetContainerElementData(byte[] pContainerStream, uint cbContainerLength, ref IntPtr pElement, byte[] pData);

        [DllImport("Irprops.cpl", SetLastError = true)]
        public static extern int BluetoothSdpGetElementData(byte[] pSdpStream, uint cbSpdStreamLength, byte[] pData);

        [DllImport("Irprops.cpl", SetLastError=true)]
		public static extern int BluetoothSdpGetString(byte[] pRecordStream, uint cbRecordLength,
  /*PSDP_STRING_DATA_TYPE*/IntPtr pStringData, ushort usStringOffset, byte[] pszString, ref uint pcchStringLength);

        internal struct SDP_STRING_TYPE_DATA
        {  
            internal ushort encoding;  
            internal ushort mibeNum;  
            internal ushort attributeID;
        }

        [DllImport("Irprops.cpl", SetLastError=true)]
        [return: MarshalAs(UnmanagedType.Bool)]
		public static extern bool BluetoothSdpEnumAttributes(
            IntPtr pSDPStream,
            int cbStreamSize,
            BluetoothEnumAttributesCallback pfnCallback,
            IntPtr pvParam);

        [return: MarshalAs(UnmanagedType.Bool)]
        internal delegate bool BluetoothEnumAttributesCallback(
            uint uAttribId,
            IntPtr pValueStream,
            int cbStreamSize,
            IntPtr pvParam);

        //Authentication functions

        [DllImport("Irprops.cpl", SetLastError = true, CharSet = CharSet.Unicode)]
        internal static extern UInt32 BluetoothRegisterForAuthentication(
            ref BLUETOOTH_DEVICE_INFO pbtdi,
            out BluetoothAuthenticationRegistrationHandle phRegHandle,
            BluetoothAuthenticationCallback pfnCallback,
            IntPtr pvParam);

        [return: MarshalAs(UnmanagedType.Bool)] // Does this have any effect?
        internal delegate bool BluetoothAuthenticationCallback(IntPtr pvParam, ref BLUETOOTH_DEVICE_INFO bdi);

        [DllImport("Irprops.cpl", SetLastError = true)]
        [return: MarshalAs(UnmanagedType.Bool)]
        [System.Security.SuppressUnmanagedCodeSecurity] // Since called from SafeHandle
        public static extern bool BluetoothUnregisterAuthentication(IntPtr hRegHandle);

        [DllImport("Irprops.cpl", SetLastError = false, CharSet = CharSet.Unicode)]
        public static extern Int32 BluetoothSendAuthenticationResponse(IntPtr hRadio, ref BLUETOOTH_DEVICE_INFO pbtdi, string pszPasskey);

		[DllImport("Irprops.cpl", SetLastError=true, CharSet=CharSet.Unicode)]
		public static extern int BluetoothRemoveDevice(byte[] pAddress);
#endif



    }

	internal enum WSAESETSERVICEOP : int
	{
		/// <summary>
		/// Register the service. For SAP, this means sending out a periodic broadcast.
		/// This is an NOP for the DNS namespace.
		/// For persistent data stores, this means updating the address information. 
		/// </summary>
		RNRSERVICE_REGISTER = 0,
		/// <summary>
		///  Remove the service from the registry.
		///  For SAP, this means stop sending out the periodic broadcast.
		///  This is an NOP for the DNS namespace.
		///  For persistent data stores this means deleting address information. 
		/// </summary>
		RNRSERVICE_DEREGISTER,
		/// <summary>
		/// Delete the service from dynamic name and persistent spaces.
		/// For services represented by multiple CSADDR_INFO structures (using the SERVICE_MULTIPLE flag), only the specified address will be deleted, and this must match exactly the corresponding CSADDR_INFO structure that was specified when the service was registered 
		/// </summary>
		RNRSERVICE_DELETE, 

	}

	[Flags()]
	internal enum LookupFlags : uint
	{
		Containers = 0x0002,
		ReturnName = 0x0010,
		ReturnAddr = 0x0100,
		ReturnBlob = 0x0200,
		FlushCache = 0x1000,
		ResService = 0x8000,
	}

	[Flags()]
	internal enum ScanMask : byte
	{
		None = 0,
		Inquiry = 1,
		Page = 2,
	}
}
