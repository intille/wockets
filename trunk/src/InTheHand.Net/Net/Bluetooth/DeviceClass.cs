// 32feet.NET - Personal Area Networking for .NET
//
// InTheHand.Net.Bluetooth.DeviceClass
// 
// Copyright (c) 2003-2008 In The Hand Ltd, All rights reserved.
// This source code is licensed under the In The Hand Community License - see License.txt

using System;
using System.Collections;
using System.Runtime.InteropServices;

namespace InTheHand.Net.Bluetooth
{
	/// <summary>
	/// Class of Device flags as assigned in the Bluetooth specifications.
	/// </summary>
	/// <remarks>Defined in Bluetooth Specifications <a href="https://www.bluetooth.org/foundry/assignnumb/document/baseband">Assigned Numbers</a>.
    /// <para>Is returned by the property <see
    /// cref="P:InTheHand.Net.Bluetooth.ClassOfDevice.Device">ClassOfDevice.Device</see>.
    /// </para>
    /// </remarks>
	public enum DeviceClass
	{
#if ! V2
        /*
#endif
#pragma warning disable 1591
#if ! V2
        */
#endif

        Miscellaneous = 0,
        
		Computer				= 0x000100,
		DesktopComputer			= 0x000104,
		ServerComputer			= 0x000108,
		LaptopComputer			= 0x00010c,
		HandheldComputer		= 0x000110,
		PdaComputer				= 0x000114,
		WearableComputer		= 0x000118,

		Phone					= 0x000200,
		CellPhone			= 0x000204,
		CordlessPhone		= 0x000208,
		SmartPhone				= 0x00020c,
		WiredPhone				= 0x000210,
		IsdnAccess				= 0x000214,

		AccessPointAvailable	= 0x000300,
		AccessPoint1To17		= 0x000320,
		AccessPoint17To33		= 0x000340,
		AccessPoint33To50		= 0x000360,
		AccessPoint50To67		= 0x000380,
		AccessPoint67To83		= 0x0003a0,
		AccessPoint83To99		= 0x0003c0,
		AccessPointNoService	= 0x0003e0,

		AudioVideoUnclassified	= 0x000400,
		AudioVideoHeadset		= 0x000404,
		AudioVideoHandsFree		= 0x000408,
		AudioVideoMicrophone	= 0x000410,
		AudioVideoLoudSpeaker	= 0x000414,
		AudioVideoHeadphones	= 0x000418,
		AudioVideoPortable		= 0x00041c,
		AudioVideoCar			= 0x000420,
		AudioVideoSetTopBox		= 0x000424,
		AudioVideoHiFi			= 0x000428,
		AudioVideoVcr			= 0x00042c,
		AudioVideoVideoCamera	= 0x000430,
		AudioVideoCamcorder		= 0x000434,
		AudioVideoMonitor		= 0x000438,
		AudioVideoDisplayLoudSpeaker	= 0x00043c,
		AudioVideoVideoConferencing		= 0x000440,
		AudioVideoGaming				= 0x000448,

		Peripheral				    = 0x000500,
		PeripheralJoystick		    = 0x000504,
		PeripheralGamepad		    = 0x000508,
		PeripheralRemoteControl		= 0x00050c,
		PeripheralSensingDevice		= 0x000510,
		PeripheralDigitizerTablet	= 0x000514,
		PeripheralCardReader		= 0x000518,

		PeripheralKeyboard			= 0x000540,
		PeripheralPointingDevice	= 0x000580,
		
		Imaging					= 0x000600,
		ImagingDisplay			= 0x000610,
		ImagingCamera			= 0x000620,
		ImagingScanner			= 0x000640,
		ImagingPrinter			= 0x000680,

		Wearable				= 0x000700,
		WearableWristWatch		= 0x000704,
		WearablePager			= 0x000708,
		WearableJacket			= 0x00070c,
		WearableHelmet			= 0x000710,
		WearableGlasses			= 0x000714,

        Toy                     = 0x000800,
        ToyRobot                = 0x000804,
        ToyVehicle              = 0x000808,
        ToyFigure               = 0x00080a,
        ToyController           = 0x00080c,
        ToyGame                 = 0x000810,

        Medical                 = 0x900,
        MedicalBloodPressureMonitor = 0x904,
        MedicalThermometer      = 0x908,
        MedicalWeighingScale    = 0x90a,
        MedicalGlucoseMeter     = 0x90c,
        MedicalPulseOximeter    = 0x910,
        MedicalHeartPulseRateMonitor = 0x914, 
        MedicalDataDisplay      = 0x918,

        Uncategorized = 0x001f00,

        //MaskServiceClasses      = 0xffe000,
        MaskMajorDeviceClass    = 0x001f00,
        MaskMinorDeviceClass    = 0x0000fc,
        MaskDeviceClass         = MaskMajorDeviceClass | MaskMinorDeviceClass,
        //MaskFormatType          = 0x000003,
	}
}

 