/**********************************************************************************************************
 * CellTSP.cs
 * Collection of methods, data structrures and enums specific to Microsoft Cellular TSP
 * Author: Alex Feinman
 * Date: 12/07/2003
 * *********************************************************************************************************/
using System;
using System.Threading;
using System.Text;
using System.Collections;
using System.Reflection;
using System.Runtime.InteropServices;
//using OpenNETCF.WinAPI;
using System.IO;

namespace Wockets.Utils.Tapi
{
    /// <summary>
    /// Summary description for CellTSP.
    /// </summary>
    public class CellTSP
    {
        public const string CELLTSP_PROVIDERINFO_STRING = "Cellular TAPI Service Provider";
        public const string CELLTSP_LINENAME_STRING = "Cellular Line";
        public const string CELLTSP_PHONENAME_STRING = "Cellular Phone";
        public CellTSP()
        {
            //
            // TODO: Add constructor logic here
            //
        }

        // Maximum string lengths
        public const int MAX_LENGTH_OPERATOR_LONG = 32;
        public const int MAX_LENGTH_OPERATOR_SHORT = 16;
        public const int MAX_LENGTH_OPERATOR_NUMERIC = 16;

        [DllImport("cellcore")]
        extern public static int lineGetCallBarringCaps(
                     IntPtr hLine,
                     out LINEBARRMODE lpdwModes,
                     out int lpdwClasses
                     );

        [DllImport("cellcore")]
        extern public static int lineGetCallBarringState(
            IntPtr hLine,
            LINEBARRMODE dwMode,
            out int lpdwClasses,
            string lpszPassword
            );

        [DllImport("cellcore")]
        extern public static int lineGetCallWaitingCaps(
            IntPtr hLine,
            out int lpdwClasses
            );

        [DllImport("cellcore")]
        extern public static int lineGetCallWaitingState(
            IntPtr hLine,
            out int lpdwClasses
            );

        [DllImport("cellcore")]
        extern public static int lineGetCurrentAddressID(
            IntPtr hLine,
            out int lpdwAddressID
            );

        [DllImport("cellcore")]
        extern public static int lineGetCurrentHSCSDStatus(
            IntPtr hLine,
            out int lpdwChannelsIn,
            out int lpdwChannelsOut,
            out int lpdwChannelCoding,
            out int lpdwAirInterfaceRate
            );

        [DllImport("cellcore")]
        extern public static int lineGetCurrentOperator(
            IntPtr hLine,
            /*LPLINEOPERATOR*/
            byte[] lpCurrentOperator
            );

        [DllImport("cellcore")]
        extern public static int lineGetCurrentSystemType(
            IntPtr hLine,
            out LINESYSTEMTYPE lpdwCurrentSystemType
            );

        [DllImport("cellcore")]
        extern public static int lineGetEquipmentState(
            IntPtr hLine,
            out int lpdwState,
            out LINERADIOSUPPORT lpdwRadioSupport
            );

        [DllImport("cellcore")]
        extern public static int lineGetGeneralInfo(
            IntPtr hLine,
            /*LPLINEGENERALINFO*/
            byte[] lpLineGeneralInfo
            );

        [DllImport("cellcore")]
        extern public static int lineGetGPRSClass(
            IntPtr hLine,
            out int lpdwClass
            );

        [DllImport("cellcore")]
        extern public static int lineGetHSCSDCaps(
            IntPtr hLine,
            out int lpdwClass,
            out int lpdwChannelsIn,
            out int lpdwChannelsOut,
            out int lpdwChannelsSum,
            out int lpdwChannelCodings
            );

        [DllImport("cellcore")]
        extern public static int lineGetHSCSDState(
            IntPtr hLine,
            out int lpdwChannelsIn,
            out int lpdwMaxChannelsIn,
            out int lpdwChannelCodings,
            out int lpdwAirInterfaceRate
            );

        [DllImport("cellcore")]
        extern public static int lineGetMuteState(
            IntPtr hLine,
            out int lpdwState
            );

        [DllImport("cellcore")]
        extern public static int lineGetNumberCalls(
            IntPtr hLine,
            out int lpdwNumActiveCalls,
            out int lpdwNumOnHoldCalls,
            out int lpdwNumOnHoldPendCalls
            );

        [DllImport("cellcore")]
        extern public static int lineGetOperatorStatus(
            IntPtr hLine,
            /*LPLINEOPERATORSTATUS*/
            byte[] lpOperatorStatus
            );

        [DllImport("cellcore")]
        extern public static int lineGetRadioPresence(
            IntPtr hLine,
            out LINERADIOPRESENCE lpdwRadioPresence
            );

        [DllImport("cellcore")]
        extern public static int lineGetRegisterStatus(
            IntPtr hLine,
            out LINEREGSTATUS lpdwRegisterStatus
            );

        [DllImport("cellcore")]
        extern public static int lineGetSendCallerIDState(
            IntPtr hLine,
            out int lpdwState
            );

        [DllImport("cellcore")]
        extern public static int lineGetUSSD(
            IntPtr hLine,
            int dwID,
            byte[] lpbUSSD,
            int dwUSSDSize,
            out int lpdwFlags
            );

        [DllImport("cellcore")]
        extern public static int lineRegister(
            IntPtr hLine,
            int dwRegisterMode,
            string lpszOperator,
            int dwOperatorFormat
            );

        //		[DllImport("cellcore")]
        //		extern public static int lineSendUSSD(
        //			IntPtr hLine,
        //			const BYTE* const lpbUSSD,
        //							int dwUSSDSize,
        //								int dwFlags
        //									);

        [DllImport("cellcore")]
        extern public static int lineSetCallBarringPassword(
            IntPtr hLine,
            int dwMode,
            string lpszOldPassword,
            string lpszNewPassword
            );

        [DllImport("cellcore")]
        extern public static int lineSetCallBarringState(
            IntPtr hLine,
            int dwMode,
            int dwClasses,
            string lpszPassword
            );

        [DllImport("cellcore")]
        extern public static int lineSetCallWaitingState(
            IntPtr hLine,
            int dwClasses,
            int dwState
            );

        [DllImport("cellcore")]
        extern public static int lineSetCurrentAddressID(
            IntPtr hLine,
            int dwAddressID
            );

        [DllImport("cellcore")]
        extern public static int lineSetEquipmentState(
            IntPtr hLine,
            int dwState
            );

        [DllImport("cellcore")]
        extern public static int lineSetGPRSClass(
            IntPtr hLine,
            int dwClass
            );

        [DllImport("cellcore")]
        extern public static int lineSetHSCSDState(
            IntPtr hLine,
            int dwChannelsIn,
            int dwMaxChannelsIn,
            int dwChannelCodings,
            int dwAirInterfaceRate
            );

        [DllImport("cellcore")]
        extern public static int lineSetMuteState(
            IntPtr hLine,
            int dwState
            );

        [DllImport("cellcore")]
        extern public static int lineSetSendCallerIDState(
            IntPtr hLine,
            int dwState
            );

        [DllImport("cellcore")]
        extern public static int lineSetPreferredOperator(
            IntPtr hLine,
            /*LPLINEOPERATOR*/
            byte[] lpOperator
            );

        [DllImport("cellcore")]
        extern public static int lineUnregister(
            IntPtr hLine
            );

    }

    public class CELLDEVCONFIG : TapiStruct
    {
        public CELLDEVCONFIG(int size)
            : base(size)
        {
            dwTotalSize = size;
        }
        public int dwTotalSize;               /* Standard TAPI structure variable */
        public int dwNeededSize;              /* Standard TAPI structure variable */
        public int dwUsedSize;                /* Standard TAPI structure variable */
        public int bBearerInfoValid;          /* TRUE iff sbiBearerInfo is valid */
        public CELLBEARERINFO cbiBearerInfo;             /* Bearer structure */
        public int bDataCompInfoValid;        /* TRUE iff sdciDataCompInfo is valid */
        public CELLDATACOMPINFO cdciDataCompInfo;          /* Data compression structure */
        public int bRadioLinkInfoValid;       /* TRUE iff srliRadioLinkInfo is valid */
        public CELLRADIOLINKINFO crliRadioLinkInfo;         /* RLP structure */
        public int bGPRSConnectionInfoValid;  /* TRUE iff sgciGPRSConnectionInfo is valid */
        public CELLGPRSCONNECTIONINFO cgciGPRSConnectionInfo;    /* GPRS connection structure */
        public int dwFlags;                   /* Bit-mask of CELLDEVCONFIG_FLAG_* constants */
    }

    public struct CELLBEARERINFO
    {
        public CELLDEVCONFIG_SPEED dwSpeed;              /* One of the CELLDEVCONFIG_SPEED_* constants */
        public int dwService;            /* One of the CELLDEVCONFIG_SERVICE_* constants */
        public int dwConnectionElement;  /* One of the CELLDEVCONFIG_CONNELEM_* constants */
    }

    public struct CELLDATACOMPINFO
    {
        public int dwDirection;        /* One of the CELLDEVCONFIG_DATACOMPDIR_* constants */
        public int dwRequired;         /* Data compression required */
        public int dwMaxDictEntries;   /* Maximum number of dictionary entries */
        public int dwMaxStringLength;  /* Maximum string length */
    }

    public struct CELLRADIOLINKINFO
    {
        public int dwVersion;             /* Version number */
        public int dwIws;                 /* IWF to MS window size  */
        public int dwMws;                 /* MS to IWF window size  */
        public int dwAckTimer;            /* Acknowledgement timer [T1] (milliseconds) */
        public int dwRetransmitAttempts;  /* Retransmit attempts [N2] */
        public int dwResequenceTimer;     /* Resequence timer [T4] (milliseconds) */
    }



    public struct CELLGPRSCONNECTIONINFO
    {
        const int CELLDEVCONFIG_MAXLENGTH_GPRSACCESSPOINTNAME = 64;
        const int CELLDEVCONFIG_MAXLENGTH_GPRSADDRESS = 64;
        const int CELLDEVCONFIG_MAXLENGTH_GPRSPARAMETERS = 32;
        public int dwProtocolType;                                                    /* One of the CELLDEVCONFIG_GPRSPROTOCOL_* constants */
        public int dwL2ProtocolType;                                                  /* One of the CELLDEVCONFIG_GPRSL2PROTOCOL_* constants */
        [Array(CELLDEVCONFIG_MAXLENGTH_GPRSACCESSPOINTNAME * 2)]
        public byte[] wszAccessPointName;   /* Logical name to select the GPRS gateway  */
        [Array(CELLDEVCONFIG_MAXLENGTH_GPRSADDRESS * 2)]
        public byte[] wszAddress;                   /* The packet address to use (if empty, then a dynamic address will be requested) */
        public int dwDataCompression;                                                 /* One of the CELLDEVCONFIG_GPRSCOMPRESSION_* constants */
        public int dwHeaderCompression;                                               /* One of the CELLDEVCONFIG_GPRSCOMPRESSION_* constants */
        [Array(CELLDEVCONFIG_MAXLENGTH_GPRSPARAMETERS * 2)]
        public byte[] szParameters;              /* Prococol-specific parameters (NULL terminated) */
        public int bRequestedQOSSettingsValid;                                        /* TRUE iff sgqsRequestedQOSSettings is valid */
        public CELLGPRSQOSSETTINGS cgqsRequestedQOSSettings;                                          /* GPRS QOS settings structure */
        public int bMinimumQOSSettingsValid;                                          /* TRUE iff sgqsMinimumQOSSettings is valid */
        public CELLGPRSQOSSETTINGS cgqsMinimumQOSSettings;                                            /* GPRS QOS settings structure */
    }

    public struct CELLGPRSQOSSETTINGS
    {
        public GPRSPRECEDENCECLASS dwPrecedenceClass;                               /* One of the CELLDEVCONFIG_GPRSPRECEDENCECLASS_* constants */
        public GPRSDELAYCLASS dwDelayClass;                                    /* One of the CELLDEVCONFIG_GPRSDELAYCLASS_* constants */
        public GPRSRELIABILITYCLASS dwReliabilityClass;                              /* One of the CELLDEVCONFIG_GPRSRELIABILITYCLASS_* constants */
        public PEAKTHRUCLASS dwPeakThruClass;                                 /* One of the CELLDEVCONFIG_GPRSPEAKTHRUCLASS_* constants */
        public MEANTHRUCLASS dwMeanThruClass;                                 /* One of the CELLDEVCONFIG_GPRSMEANTHRUCLASS_* constants */
    }

    public enum GPRSPRECEDENCECLASS
    {
        UNKNOWN = (0x00000000),  // Unknown
        SUBSCRIBED = (0x00000001), // Subscribed value stored in network
        HIGH = (0x00000002),  // High priority
        NORMAL = (0x00000003),  // Normal priority
        LOW = (0x00000004),  // Low priority
    }

    public enum GPRSDELAYCLASS
    {
        UNKNOWN = (0x00000000),  // Unknown
        SUBSCRIBED = (0x00000001),
        PREDICTIVE1 = (0x00000002),
        PREDICTIVE2 = (0x00000003),
        PREDICTIVE3 = (0x00000004),
        BESTEFFORT = (0x00000005),
    }

    public enum GPRSRELIABILITYCLASS
    {
        CLASS_UNKNOWN = (0x00000000),  // Unknown
        CLASS_SUBSCRIBED = (0x00000001),
        CLASS_1 = (0x00000002),
        CLASS_2 = (0x00000003),
        CLASS_3 = (0x00000004),
        CLASS_4 = (0x00000005),
        CLASS_5 = (0x00000006),
    }

    public enum PEAKTHRUCLASS
    {
        CLASS_UNKNOWN = (0x00000000),  // Unknown
        CLASS_SUBSCRIBED = (0x00000001),
        CLASS_8000 = (0x00000002),  // kbit/second
        CLASS_16000 = (0x00000003),
        CLASS_32000 = (0x00000004),
        CLASS_64000 = (0x00000005),
        CLASS_128000 = (0x00000006),
        CLASS_256000 = (0x00000007),
        CLASS_512000 = (0x00000008),
        CLASS_1024000 = (0x00000009),
        CLASS_2048000 = (0x0000000a),
    }

    public enum MEANTHRUCLASS
    {
        CLASS_UNKNOWN = (0x00000000),  // Unknown
        CLASS_SUBSCRIBED = (0x00000001),
        CLASS_100 = (0x00000002),  // octets/hour
        CLASS_200 = (0x00000003),
        CLASS_500 = (0x00000004),
        CLASS_1000 = (0x00000005),
        CLASS_2000 = (0x00000006),
        CLASS_5000 = (0x00000007),
        CLASS_10000 = (0x00000008),
        CLASS_20000 = (0x00000009),
        CLASS_50000 = (0x0000000a),
        CLASS_100000 = (0x0000000b),
        CLASS_200000 = (0x0000000c),
        CLASS_500000 = (0x0000000d),
        CLASS_1000000 = (0x0000000e),
        CLASS_2000000 = (0x0000000f),
        CLASS_5000000 = (0x00000010),
        CLASS_10000000 = (0x00000011),
        CLASS_20000000 = (0x00000012),
        CLASS_50000000 = (0x00000013),
        CLASS_DONTCARE = (0x00000014),  // Best effort
    }

    public enum CELLDEVCONFIG_SPEED
    {
        SPEED_UNKNOWN = (0x00000000),  // Unknown speed
        SPEED_AUTO = (0x00000001),  // Automatic selection of speed
        SPEED_300_V21 = (0x00000002),  // 300 bps      (V.21)
        SPEED_300_V110 = (0x00000003),  // 300 bps      (V.100)
        SPEED_1200_V22 = (0x00000004),  // 1200 bps     (V.22)
        SPEED_1200_75_V23 = (0x00000005),  // 1200/75 bps  (V.23)
        SPEED_1200_V110 = (0x00000006),  // 1200 bps     (V.100)
        SPEED_1200_V120 = (0x00000007),  // 1200 bps     (V.120)
        SPEED_2400_V22BIS = (0x00000008),  // 2400 bps     (V.22bis)
        SPEED_2400_V26TER = (0x00000009),  // 2400 bps     (V.26ter)
        SPEED_2400_V110 = (0x0000000a),  // 2400 bps     (V.110 or X.31 flag stuffing)
        SPEED_2400_V120 = (0x0000000b),  // 2400 bps     (V.120)
        SPEED_4800_V32 = (0x0000000c),  // 4800 bps     (V.32)
        SPEED_4800_V110 = (0x0000000d),  // 4800 bps     (V.110 or X.31 flag stuffing)
        SPEED_4800_V120 = (0x0000000e),  // 4800 bps     (V.120)
        SPEED_9600_V32 = (0x0000000f),  // 9600 bps     (V.32)
        SPEED_9600_V34 = (0x00000010),  // 9600 bps     (V.34)
        SPEED_9600_V110 = (0x00000011),  // 9600 bps     (V.110 or X.31 flag stuffing)
        SPEED_9600_V120 = (0x00000012),  // 9600 bps     (V.120)
        SPEED_14400_V34 = (0x00000013),  // 14400 bps    (V.34)
        SPEED_14400_V110 = (0x00000014),  // 14400 bps    (V.100 or X.31 flag stuffing)
        SPEED_14400_V120 = (0x00000015),  // 14400 bps    (V.120)
        SPEED_19200_V34 = (0x00000016),  // 19200 bps    (V.34)
        SPEED_19200_V110 = (0x00000017),  // 19200 bps    (V.110 or X.31 flag stuffing)
        SPEED_19200_V120 = (0x00000018),  // 19200 bps    (V.120)
        SPEED_28800_V34 = (0x00000019),  // 28800 bps    (V.34)
        SPEED_28800_V110 = (0x0000001a),  // 28800 bps    (V.110 or X.31 flag stuffing)
        SPEED_28800_V120 = (0x0000001b),  // 28800 bps    (V.120)
        SPEED_38400_V110 = (0x0000001c),  // 38400 bps    (V.110 or X.31 flag stuffing)
        SPEED_38400_V120 = (0x0000001d),  // 38400 bps    (V.120)
        SPEED_48000_V110 = (0x0000001e),  // 48000 bps    (V.110 or X.31 flag stuffing)
        SPEED_48000_V120 = (0x0000001f),  // 48000 bps    (V.120)
        SPEED_56000_V110 = (0x00000020),  // 56000 bps    (V.110 or X.31 flag stuffing)
        SPEED_56000_V120 = (0x00000021),  // 56000 bps    (V.120)
        SPEED_56000_TRANSP = (0x00000022),  // 56000 bps    (bit transparent)
        SPEED_64000_TRANSP = (0x00000023),  // 64000 bps    (bit transparent)
    }


    // Line barring modes
    [Flags]
    public enum LINEBARRMODE
    {
        OUT = 0x00000001,
        OUT_INT = 0x00000002,
        OUT_INTEXTOHOME = 0x00000004,
        IN = 0x00000008,
        IN_ROAM = 0x00000010,
        IN_NOTINSIM = 0x00000020,
        ALL = 0x00000040,
        ALL_OUT = 0x00000080,
        ALL_IN = 0x00000100,
    }

    // Line call-waiting states
    [Flags]
    public enum LINECALLWAITING
    {
        ENABLED = 0x00000001,
        DISABLED = 0x00000002,
    }

    // Line capability classes
    [Flags]
    public enum LINECAPSCLASS
    {
        VOICE = 0x00000001,
        DATA = 0x00000002,
        FAX = 0x00000004,
        SMS = 0x00000008,
        SYNCDATA = 0x00000010,
        ASYNCDATA = 0x00000020,
        PACKET = 0x00000040,
        PAD = 0x00000080,
        ALL = 0x000000ff,
    }

    // Line equipment states
    public enum LINEEQUIPSTATE
    {
        MINIMUM = 0x00000001,
        RXONLY = 0x00000002,
        TXONLY = 0x00000003,
        NOTXRX = 0x00000004,
        FULL = 0x00000005,
    }

    // Line GPRS class types
    public enum LINEGPRSCLASS
    {
        GSMANDGPRS = 0x00000001,
        GSMORGPRS = 0x00000002,
        GSMORGPRS_EXCLUSIVE = 0x00000003,
        GPRSONLY = 0x00000004,
        GSMONLY = 0x00000005,
    }

    // Line GPRS class changed types
    [Flags]
    public enum LINEGPRSCLASSCHANGED
    {
        NETWORK = 0x00000001,
        RADIO = 0x00000002,
    }

    // Line HSCSD air-rates
    public enum LINEHSCSDAIRRATE
    {
        RATE_9600 = 0x00000001,
        RATE_14400 = 0x00000002,
        RATE_19200 = 0x00000003,
        RATE_28800 = 0x00000004,
        RATE_38400 = 0x00000005,
        RATE_43200 = 0x00000006,
        RATE_57600 = 0x00000007,
    }

    // Line HSCSD codings
    public enum LINEHSCSDCODING
    {
        CODING_4800 = 0x00000001,
        CODING_9600 = 0x00000002,
        CODING_14400 = 0x00000004,
    }

    // Line mute states
    public enum LINEMUTESTATE
    {
        MUTEENABLED = 0x00000001,
        MUTEDISABLED = 0x00000002,
    }

    // Line operator formats
    [Flags]
    public enum LINEOPFORMAT
    {
        NONE = 0x00000000,
        ALPHASHORT = 0x00000001,
        ALPHALONG = 0x00000002,
        NUMERIC = 0x00000004,
    }

    // Line operator statuses
    public enum LINEOPSTATUS
    {
        UNKNOWN = 0x00000000,
        AVAILABLE = 0x00000001,
        CURRENT = 0x00000002,
        FORBIDDEN = 0x00000003,
    }

    // Line radio presence states
    public enum LINERADIOPRESENCE
    {
        PRESENT = 0x00000001,
        NOTPRESENT = 0x00000002,
    }

    // Line radio support states
    public enum LINERADIOSUPPORT
    {
        OFF = 0x00000001,
        ON = 0x00000002,
        UNKNOWN = 0x00000003,
    }

    // Line register modes
    public enum LINEREGMODE
    {
        AUTOMATIC = 0x00000001,
        MANUAL = 0x00000002,
        MANAUTO = 0x00000003,
    }

    // Line register status
    public enum LINEREGSTATUS
    {
        UNKNOWN = 0x00000001,
        DENIED = 0x00000002,
        UNREGISTERED = 0x00000003,
        ATTEMPTING = 0x00000004,
        HOME = 0x00000005,
        ROAM = 0x00000006,
        DIGITAL = 0x00000007,
        ANALOG = 0x00000008,
    }

    // Line send caller-ID states
    public enum LINESENDCALLERID
    {
        ENABLED = 0x00000001,
        DISABLED = 0x00000002,
    }

    [Flags]
    public enum LINESYSTEMTYPE
    {
        // Line system types, CDMA
        NONE = 0x00000000,
        IS95A = 0x00000001,
        IS95B = 0x00000002,
        ONEXRTTPACKET = 0x00000004,
        // Line system types, GSM
        GSM = 0x00000008,
        GPRS = 0x00000010,
    }


    // Line USSD flags
    [Flags]
    public enum LINEUSSDFLAG
    {
        ACTIONREQUIRED = 0x00000001,
        ACTIONNOTNEEDED = 0x00000002,
        TERMINATED = 0x00000004,
        OTHERCLIENTRESPONDED = 0x00000008,
        UNSUPPORTED = 0x00000010,
        TIMEOUT = 0x00000020,
        ENDSESSION = 0x00000040,
    }

    // Special LINEOPERATOR index values
    public enum LINEOPERATOROPTIONS
    {
        LINEOPERATOR_USEFIRSTAVAILABLEINDEX = (-1),
    }



    public enum LINEDEVSPECIFIC_CELLTSP
    {
        // LINE_DEVSPECIFIC message types
        /// <summary>
        /// dwParam1 = LINE_EQUIPSTATECHANGE
        /// dwParam2 = One of the * constants
        /// dwParam3 = One of the * constants
        /// </summary>
        LINE_EQUIPSTATECHANGE = 0x00000100,

        /// <summary>
        /// dwParam1 = LINE_GPRSCLASS
        /// dwParam2 = One of the * constants
        /// dwParam3 = One of the * constants
        /// </summary>
        LINE_GPRSCLASS = 0x00000101,

        /// <summary>
        /// dwParam1 = LINE_GPRSREGISTERSTATE
        /// dwParam2 = One of the * constants
        /// dwParam3 Unused
        /// </summary>
        LINE_GPRSREGISTERSTATE = 0x00000102,

        /// <summary>
        /// dwParam1 = LINE_RADIOPRESENCE
        /// dwParam2 = One of the * constants
        /// dwParam3 Unused
        /// </summary>
        LINE_RADIOPRESENCE = 0x00000103,

        /// <summary>
        /// dwParam1 = LINE_REGISTERSTATE
        /// dwParam2 = One of the * constants
        /// dwParam3 Unused
        /// </summary>
        LINE_REGISTERSTATE = 0x00000104,

        /// <summary>
        /// dwParam1 = LINE_USSD
        /// dwParam2 = Message identifier
        /// dwParam3 = Size in bytes of message
        /// </summary>
        LINE_USSD = 0x00000105,

        /// <summary>
        /// dwParam1 = LINE_CURRENTLINECHANGE
        /// dwParam2 = New line identifier
        /// dwParam3 = New address ID
        /// </summary>
        LINE_CURRENTLINECHANGE = 0x00000106,

        /// <summary>
        /// dwParam1 = LINE_CURRENTSYSTEMCHANGE
        /// dwParam2 = New system coverage (*)
        /// dwParam3 = unused
        /// </summary>
        LINE_CURRENTSYSTEMCHANGE = 0x00000107,
    }


    // Structures
    public class LINEOPERATOR
    {
        public LINEOPERATOR()
        {
            lpszLongName = new byte[CellTSP.MAX_LENGTH_OPERATOR_LONG * 2];
            lpszShortName = new byte[CellTSP.MAX_LENGTH_OPERATOR_SHORT * 2];
            lpszNumName = new byte[CellTSP.MAX_LENGTH_OPERATOR_NUMERIC * 2];
        }
        public int dwIndex;
        public int dwValidFields;
        public int dwStatus;
        [Array(CellTSP.MAX_LENGTH_OPERATOR_LONG * 2)]
        public byte[] lpszLongName;
        [Array(CellTSP.MAX_LENGTH_OPERATOR_SHORT * 2)]
        public byte[] lpszShortName;
        [Array(CellTSP.MAX_LENGTH_OPERATOR_NUMERIC * 2)]
        public byte[] lpszNumName;
        public int SizeOf { get { return 3 * Marshal.SizeOf(typeof(int)) + (CellTSP.MAX_LENGTH_OPERATOR_LONG + CellTSP.MAX_LENGTH_OPERATOR_SHORT + CellTSP.MAX_LENGTH_OPERATOR_NUMERIC) * 2; } }
        public string LongName { get { return Encoding.Unicode.GetString(lpszLongName, 0, lpszLongName.Length).TrimEnd('\0'); } }
        public string ShortName { get { return Encoding.Unicode.GetString(lpszShortName, 0, lpszShortName.Length).TrimEnd('\0'); } }
        public string NumName { get { return Encoding.Unicode.GetString(lpszNumName, 0, lpszNumName.Length).TrimEnd('\0'); } }
    }

    public class LINEOPERATORSTATUS : TapiStruct
    {
        public LINEOPERATORSTATUS(int size)
            : base(size)
        {
            dwTotalSize = size;
        }
        public int dwTotalSize;
        public int dwNeededSize;
        public int dwUsedSize;
        public int dwPreferredCount;
        public int dwPreferredSize;
        public int dwPreferredOffset;
        public int dwAvailableCount;
        public int dwAvailableSize;
        public int dwAvailableOffset;
    }

    public class LINEGENERALINFO : TapiStruct
    {
        public LINEGENERALINFO(int size)
            : base(size)
        {
            dwTotalSize = size;
        }
        public int dwTotalSize;
        public int dwNeededSize;
        public int dwUsedSize;
        public int dwManufacturerSize;
        public int dwManufacturerOffset;
        public int dwModelSize;
        public int dwModelOffset;
        public int dwRevisionSize;
        public int dwRevisionOffset;
        public int dwSerialNumberSize;
        public int dwSerialNumberOffset;
        public int dwSubscriberNumberSize;
        public int dwSubscriberNumberOffset;

        public string Manufacturer { get { return dwManufacturerSize == 0 ? "" : Encoding.Unicode.GetString(Data, dwManufacturerOffset, dwManufacturerSize); } }
        public string Model { get { return dwModelSize == 0 ? "" : Encoding.Unicode.GetString(Data, dwModelOffset, dwModelSize); } }
        public string Revision { get { return dwRevisionSize == 0 ? "" : Encoding.Unicode.GetString(Data, dwRevisionOffset, dwRevisionSize); } }
        public string SerialNumber { get { return dwSerialNumberSize == 0 ? "" : Encoding.Unicode.GetString(Data, dwSerialNumberOffset, dwSerialNumberSize); } }
        public string SubscriberNumber { get { return dwSubscriberNumberSize == 0 ? "" : Encoding.Unicode.GetString(Data, dwSubscriberNumberOffset, dwSubscriberNumberSize); } }
    }


}