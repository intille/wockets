// 32feet.NET - Personal Area Networking for .NET
//
// InTheHand.Net.Bluetooth.Manufacturer
// 
// Copyright (c) 2003-2006 In The Hand Ltd, All rights reserved.
// This source code is licensed under the In The Hand Community License - see License.txt

namespace InTheHand.Net.Bluetooth
{
	/// <summary>
	/// Manufacturer codes.
	/// </summary>
	/// <remarks>Defined in Bluetooth Specifications <a href="https://www.bluetooth.org/foundry/assignnumb/document/company_identifiers">Assigned Numbers</a>.</remarks>
	public enum Manufacturer : short
    {
#if ! V2
        /*
#endif
#pragma warning disable 1591
#if ! V2
        */
#endif

        Unknown = -1,

        Ericsson        = 0,
        Nokia           = 1,
        Intel           = 2,
        Ibm             = 3,
        Toshiba         = 4,
        ThreeCom        = 5,
        Microsoft       = 6,
        Lucent          = 7,
        Motorola        = 8,
        InfineonTechnologies = 9,
        CambridgeSiliconRadio = 10,
        SiliconWave     = 11,
        Digianswer      = 12,
        TexasInstruments = 13,
        ParthusTechnologies = 14,
        Broadcom        = 15,
        Mitel           = 16,
        Widcomm         = 17,
        Zeevo           = 18,
        Atmel           = 19,
        Mitsubishi      = 20,
        RtxTelecom     = 21,
        KCTechnology   = 22,
        Newlogic        = 23,
        Transilica      = 24,
        RohdeSchwarz   = 25,
        TtpCom          = 26,
        Signia          = 27,
        Conexant        = 28,
        Qualcomm        = 29,
        Invetel        = 30,
        AvmBerlin      = 31,
        BandSpeed       = 32,
        Mansella        = 33,
        Nec             = 34,
        WavePlusTechnology = 35,
        Alcatel         = 36,
        PhilipsSemiconductor  = 37,
        CTechnologies  = 38,
        OpenInterface  = 39,
        RFMicroDevices = 40,
        Hitachi        = 41,
        SymbolTechnologies = 42,
        Tenovis        = 43,
        MacronixInternational = 44,
		GctSemiconducter = 45,
		NorwoodSystems = 46,
		MewTelTechnology = 47,
		STMicroelectronics = 48,
		Synopsys = 49,
		RedM = 50,
		Commil = 51,
		Catc = 52,
		Eclipse = 53,
		RenesasTechnology = 54,
		Mobilian = 55,
		Terax = 56,
		IntegratedSystemSolution = 57,
		Matsushita = 58,
		Gennum = 59,
		ResearchInMotion = 60,
		IPextreme = 61,
		SystemsAndChips = 62,
        BluetoothSig = 63,
        SeikoEpson = 64,
        IntegratedSiliconSolutionTaiwan = 65,
        Conwise = 66,
        Parrot = 67,
        SocketMobile = 68,
        AtherosCommunications = 69,
        MediaTek = 70, 
        Bluegiga = 71,
        MarvellTechnologyGroup = 72,
        ThreeDSP = 73,
        AccelSemiconductor = 74,
        ContinentalAutomotiveSystems = 75,
        Apple = 76,
        StaccatoCommunications = 77,

		// <summary>
		// For use in internal and interoperability tests before a Company ID has been assigned.
		// May not be used in products.
		// Only used in Link Manager testing.
		// </summary>
		//InternalUse    = 65535,
	}
}
