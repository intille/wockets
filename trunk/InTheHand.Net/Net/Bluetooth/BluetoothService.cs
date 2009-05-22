// 32feet.NET - Personal Area Networking for .NET
//
// InTheHand.Net.Bluetooth.BluetoothService
// 
// Copyright (c) 2003-2006 In The Hand Ltd, All rights reserved.
// This source code is licensed under the In The Hand Community License - see License.txt

using System;

namespace InTheHand.Net.Bluetooth
{
	/// <summary>
	/// Standard Bluetooth Profile identifiers.
	/// </summary>
#if V2
    public static class BluetoothService
    {
#else
	public class BluetoothService
	{
        private BluetoothService() {}
#endif
        /// <summary>
		/// Represents an empty service Guid.
		/// </summary>
		public static readonly Guid Empty = Guid.Empty;
		

		/// <summary>
		/// Represents the base Guid from which all standard Bluetooth profiles are derived - not used for connections.
		/// </summary>
		public static readonly Guid BluetoothBase = new Guid(0x00000000, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);

#if ! V2
        /*
#endif
#pragma warning disable 1591
#if ! V2
        */
#endif
        //Considering moving all the protocol definitions to a separate class from the profiles...
        public static readonly Guid SdpProtocol = new Guid(0x00000001, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		public static readonly Guid UdpProtocol = new Guid(0x00000002, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		public static readonly Guid RFCommProtocol = new Guid(0x00000003, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		public static readonly Guid TcpProtocol = new Guid(0x00000004, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		public static readonly Guid TcsBinProtocol = new Guid(0x00000005, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		public static readonly Guid TcsAtProtocol = new Guid(0x00000006, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		public static readonly Guid ObexProtocol = new Guid(0x00000008, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		public static readonly Guid IPProtocol = new Guid(0x00000009, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		public static readonly Guid FtpProtocol = new Guid(0x0000000A, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		public static readonly Guid HttpProtocol = new Guid(0x0000000C, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		public static readonly Guid WspProtocol = new Guid(0x0000000E, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
        public static readonly Guid BnepProtocol = new Guid(0x0000000F, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
        public static readonly Guid UpnpProtocol = new Guid(0x00000010, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
        public static readonly Guid HidpProtocol = new Guid(0x00000011, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
        public static readonly Guid HardcopyControlChannelProtocol = new Guid(0x00000012, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
        public static readonly Guid HardcopyDataChannelProtocol = new Guid(0x00000014, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
        public static readonly Guid HardcopyNotificationProtocol = new Guid(0x00000016, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
        public static readonly Guid AvctpProtocol = new Guid(0x00000017, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
        public static readonly Guid AvdtpProtocol = new Guid(0x00000019, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
        public static readonly Guid CmtpProtocol = new Guid(0x0000001B, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
        public static readonly Guid UdiCPlaneProtocol = new Guid(0x0000001D, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
        public static readonly Guid McapControlChannelProtocol = new Guid(0x0000001E, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
        public static readonly Guid McapDataChannelProtocol = new Guid(0x0000001F, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);

        public static readonly Guid L2CapProtocol = new Guid(0x00000100, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		

		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid ServiceDiscoveryServer = new Guid(0x00001000, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid BrowseGroupDescriptor = new Guid(0x00001001, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid PublicBrowseGroup = new Guid(0x00001002, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// Provides a basic Serial emulation connect over Bluetooth.
		/// </summary>
		public static readonly Guid SerialPort = new Guid(0x00001101, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		
		/// <summary>
		/// Used to establish PPP connections over RFComm channels.
		/// </summary>
		public static readonly Guid LanAccessUsingPpp = new Guid(0x00001102, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid DialupNetworking = new Guid(0x00001103, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid IrMCSync = new Guid(0x00001104, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// Used for sending binary objects between devices.
		/// </summary>
		public static readonly Guid ObexObjectPush = new Guid(0x00001105, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// OBEX version of an FTP server
		/// </summary>
		public static readonly Guid ObexFileTransfer = new Guid(0x00001106, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid IrMCSyncCommand = new Guid(0x00001107, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		
		/// <summary>
		/// Supports Bluetooth headset devices.
		/// </summary>
		public static readonly Guid Headset = new Guid(0x00001108, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid CordlessTelephony = new Guid(0x00001109, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid AudioSource = new Guid(0x0000110A, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid AudioSink = new Guid(0x0000110B, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid AVRemoteControlTarget = new Guid(0x0000110C, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid AdvancedAudioDistribution = new Guid(0x0000110D, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid AVRemoteControl = new Guid(0x0000110E, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid VideoConferencing = new Guid(0x0000110F, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid Intercom = new Guid(0x00001110, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid Fax = new Guid(0x00001111, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid HeadsetAudioGateway = new Guid(0x00001112, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid Wap = new Guid(0x00001113, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid WapClient = new Guid(0x00001114, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid Panu = new Guid(0x00001115, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid Nap = new Guid(0x00001116, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid GN = new Guid(0x00001117, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid DirectPrinting = new Guid(0x00001118, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid ReferencePrinting = new Guid(0x00001119, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid Imaging = new Guid(0x0000111A, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid ImagingResponder = new Guid(0x0000111B, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid ImagingAutomaticArchive = new Guid(0x0000111C, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid ImagingReferenceObjects = new Guid(0x0000111D, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		
		/// <summary>
		/// Supports hands free kits such as a car kits which provide audio and more advanced call control than the Headset profile.
		/// </summary>
		public static readonly Guid Handsfree = new Guid(0x0000111E, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid HandsfreeAudioGateway = new Guid(0x0000111F, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid DirectPrintingReferenceObjects = new Guid(0x00001120, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid ReflectedUI = new Guid(0x00001121, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// Used for printing simple text, HTML, vCard objects and similar.
		/// </summary>
		public static readonly Guid BasicPrinting = new Guid(0x00001122, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid PrintingStatus = new Guid(0x00001123, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// Supports human interface devices such as keyboards and mice.
		/// </summary>
		public static readonly Guid HumanInterfaceDevice = new Guid(0x00001124, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid HardcopyCableReplacement = new Guid(0x00001125, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid HardcopyCableReplacementPrint = new Guid(0x00001126, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid HardcopyCableReplacementScan = new Guid(0x00001127, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
        /// Common_ISDN_Access
		/// </summary>
		public static readonly Guid CommonIsdnAccess = new Guid(0x00001128, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid VideoConferencingGW = new Guid(0x00001129, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
        /// UDI_MT
		/// </summary>
		public static readonly Guid UdiMT = new Guid(0x0000112A, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
        /// UDI_TA
		/// </summary>
		public static readonly Guid UdiTA = new Guid(0x0000112B, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid AudioVideo = new Guid(0x0000112C, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
        /// SIM_Access
		/// </summary>
		public static readonly Guid SimAccess = new Guid(0x0000112D, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
        /// <summary>
        /// Phonebook Access - PCE
        /// </summary>
        public static readonly Guid PhonebookAccessPce = new Guid(0x0000112E, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
        /// <summary>
        /// Phonebook Access - PSE
        /// </summary>
        public static readonly Guid PhonebookAccessPse = new Guid(0x0000112F, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB); 
        /// <summary>
        /// Phonebook Access
        /// </summary>
        public static readonly Guid PhonebookAccess = new Guid(0x00001130, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB); 

		/// <summary>
        /// Bluetooth Device Identification.
		/// </summary>
		public static readonly Guid PnPInformation = new Guid(0x00001200, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid GenericNetworking = new Guid(0x00001201, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid GenericFileTransfer = new Guid(0x00001202, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid GenericAudio = new Guid(0x00001203, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid GenericTelephony = new Guid(0x00001204, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid UPnp = new Guid(0x00001205, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// 
		/// </summary>
		public static readonly Guid UPnpIP = new Guid(0x00001206, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
        /// ESDP_UPNP_IP_PAN
		/// </summary>
		public static readonly Guid UPnpIPPan = new Guid(0x00001300, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
        /// ESDP_UPNP_IP_LAP
		/// </summary>
		public static readonly Guid UPnpIPLap = new Guid(0x00001301, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
        /// ESDP_UPNP_L2CAP
		/// </summary>
		public static readonly Guid UPnpIPL2Cap = new Guid(0x00001302, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		
		/// <summary>
        /// Video Distribution Profile - Source
		/// </summary>
		public static readonly Guid VideoSource = new Guid(0x00001303, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
        /// Video Distribution Profile - Sink
		/// </summary>
		public static readonly Guid VideoSink = new Guid(0x00001304, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
		/// <summary>
		/// Video Distribution Profile
		/// </summary>
		public static readonly Guid VideoDistribution = new Guid(0x00001305, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);

        /// <summary>
        /// Health Device Profile (HDP)
		/// </summary>
		public static readonly Guid HealthDevice = new Guid(0x00001400, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
        /// <summary>
        /// Health Device Profile (HDP) - Source
		/// </summary>
        public static readonly Guid HealthDeviceSource = new Guid(0x00001401, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
        /// <summary>
        /// Health Device Profile (HDP) - Sink
		/// </summary>
        public static readonly Guid HealthDeviceSink = new Guid(0x00001402, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);


        #region Get Name
        /// <summary>
        /// Retrieves the name of the Service Class UUID that has the specified value. 
        /// </summary>
        /// <param name="uuid">
        /// The service class UUID as a <see cref="T:System.Guid"/>.
        /// </param>
        /// <returns>
        /// A string containing the name of the service class whose UUID value is <paramref name="uuid"/>,
        /// or a null reference (<c>Nothing</c> in Visual Basic) if no such constant is found.
        /// </returns>
        public static String GetName(Guid uuid)
        {
            System.Reflection.FieldInfo[] fields
                = typeof(BluetoothService).GetFields(System.Reflection.BindingFlags.Public | System.Reflection.BindingFlags.Static);
            foreach (System.Reflection.FieldInfo curField in fields)
            {
                object rawValue = curField.GetValue(null);
                Guid fieldValue = (Guid)rawValue;
                if (fieldValue.Equals(uuid))
                {
                    string fieldName = curField.Name;
                    return fieldName;
                }
            }//for

            return null;
        }
        

        /// <summary>
        /// Retrieves the name of the Service Class UUID that has the specified value. 
        /// </summary>
        /// <param name="uuid16">
        /// The service class UUID in the 16-bit UUID short form as a <see cref="T:System.Int16"/>.
        /// </param>
        /// <returns>
        /// A string containing the name of the service class whose UUID value is <paramref name="uuid"/>,
        /// or a null reference (<c>Nothing</c> in Visual Basic) if no such constant is found.
        /// </returns>
        public static String GetName(Int16 uuid16)
        {
            return GetName(CreateBluetoothUuid(uuid16));
        }

        /// <summary>
        /// Retrieves the name of the Service Class UUID that has the specified value. 
        /// </summary>
        /// <param name="uuid16">
        /// The service class UUID in the 16-bit short UUID form as a <see cref="T:System.UInt16"/>.
        /// </param>
        /// <returns>
        /// A string containing the name of the service class whose UUID value is <paramref name="uuid"/>,
        /// or a null reference (<c>Nothing</c> in Visual Basic) if no such constant is found.
        /// </returns>
        [CLSCompliant(false)] //use Int32 overload instead
        public static String GetName(UInt16 uuid16)
        {
            return GetName(CreateBluetoothUuid(uuid16));
        }

        /// <summary>
        /// Retrieves the name of the Service Class UUID that has the specified value. 
        /// </summary>
        /// <param name="uuid32">
        /// The service class UUID in the 32-bit short UUID form as a <see cref="T:System.Int32"/>.
        /// </param>
        /// <returns>
        /// A string containing the name of the service class whose UUID value is <paramref name="uuid"/>,
        /// or a null reference (<c>Nothing</c> in Visual Basic) if no such constant is found.
        /// </returns>
        public static String GetName(Int32 uuid32)
        {
            return GetName(CreateBluetoothUuid(uuid32));
        }

        /// <summary>
        /// Retrieves the name of the Service Class UUID that has the specified value. 
        /// </summary>
        /// <param name="uuid32">
        /// The service class UUID in the 32-bit UUID short form as a <see cref="T:System.UInt32"/>.
        /// </param>
        /// <returns>
        /// A string containing the name of the service class whose UUID value is <paramref name="uuid"/>,
        /// or a null reference (<c>Nothing</c> in Visual Basic) if no such constant is found.
        /// </returns>
        [CLSCompliant(false)] //use Int32 overload instead
        public static String GetName(UInt32 uuid32)
        {
            return GetName(CreateBluetoothUuid(uuid32));
        }
        #endregion

        #region Create Bluetooth UUID
        /// <summary>
        /// Create a full 128-bit Service class UUID from its 16-bit short form.
        /// </summary>
        /// <param name="uuid16">
        /// The service class UUID in the 16-bit UUID short form as a <see cref="T:System.Int16"/>.
        /// </param>
        /// <returns>
        /// A <see cref="T:System.Guid"/> containing the full 128-bit form of the
        /// supplied Bluetooth service class UUID.
        /// </returns>
        public static Guid CreateBluetoothUuid(Int16 uuid16)
        {
            return CreateBluetoothUuid(unchecked((Int32)uuid16));
        }

        /// <summary>
        /// Create a full 128-bit Service class UUID from its 16-bit short form.
        /// </summary>
        /// <param name="uuid16">
        /// The service class UUID in the 16-bit UUID short form as a <see cref="T:System.UInt16"/>.
        /// </param>
        /// <returns>
        /// A <see cref="T:System.Guid"/> containing the full 128-bit form of the
        /// supplied Bluetooth service class UUID.
        /// </returns>
        [CLSCompliant(false)] //use Int16 overload instead
        public static Guid CreateBluetoothUuid(UInt16 uuid16)
        {
            return CreateBluetoothUuid((UInt32)uuid16);
        }

        /// <summary>
        /// Create a full 128-bit Service class UUID from its 16-bit short form.
        /// </summary>
        /// <param name="uuid32">
        /// The service class UUID in the 32-bit UUID short form as a <see cref="T:System.Int32"/>.
        /// </param>
        /// <returns>
        /// A <see cref="T:System.Guid"/> containing the full 128-bit form of the
        /// supplied Bluetooth service class UUID.
        /// </returns>
        public static Guid CreateBluetoothUuid(Int32 uuid32)
        {
            // Base UUID: 00000000-0000-1000-8000-00805f9b34fb.
            Guid uuid = new Guid(uuid32, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5f, 0x9b, 0x34, 0xfb);
            return uuid;
        }

        /// <summary>
        /// Create a full 128-bit Service class UUID from its 16-bit short form.
        /// </summary>
        /// <param name="uuid32">
        /// The service class UUID in the 32-bit UUID short form as a <see cref="T:System.UInt32"/>.
        /// </param>
        /// <returns>
        /// A <see cref="T:System.Guid"/> containing the full 128-bit form of the
        /// supplied Bluetooth service class UUID.
        /// </returns>
        [CLSCompliant(false)] //use Int32 overload instead
        public static Guid CreateBluetoothUuid(UInt32 uuid32)
        {
            return CreateBluetoothUuid(unchecked((Int32)uuid32));
        }
        #endregion
    }
}
