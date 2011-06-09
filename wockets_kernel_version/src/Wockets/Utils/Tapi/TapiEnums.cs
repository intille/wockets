using System;
using System.Reflection;

namespace Wockets.Utils.Tapi
{
    public enum LINEINITIALIZEEXOPTIONS
    {
        USEHIDDENWINDOW = 0x00000001,  // TAPI v2.0
        USEEVENT = 0x00000002,  // TAPI v2.0
        USECOMPLETIONPORT = 0x00000003,  // TAPI v2.0
    }

    [Flags]
    public enum LINEMEDIACONTROL
    {
        NONE = 0x00000001,
        START = 0x00000002,
        RESET = 0x00000004,
        PAUSE = 0x00000008,
        RESUME = 0x00000010,
        RATEUP = 0x00000020,
        RATEDOWN = 0x00000040,
        RATENORMAL = 0x00000080,
        VOLUMEUP = 0x00000100,
        VOLUMEDOWN = 0x00000200,
        VOLUMENORMAL = 0x00000400,
    }

    [Flags]
    public enum LINEMEDIAMODE
    {
        UNKNOWN = 0x00000002,
        INTERACTIVEVOICE = 0x00000004,
        AUTOMATEDVOICE = 0x00000008,
        DATAMODEM = 0x00000010,
        G3FAX = 0x00000020,
        TDD = 0x00000040,
        G4FAX = 0x00000080,
        DIGITALDATA = 0x00000100,
        TELETEX = 0x00000200,
        VIDEOTEX = 0x00000400,
        TELEX = 0x00000800,
        MIXED = 0x00001000,
        ADSI = 0x00002000,
        VOICEVIEW = 0x00004000,      // TAPI v1.4
        LAST_LINEMEDIAMODE = 0x00004000,
    }


    public enum LINEERR : uint
    {
        ALLOCATED = 0x80000001,
        BADDEVICEID = 0x80000002,
        BEARERMODEUNAVAIL = 0x80000003,
        CALLUNAVAIL = 0x80000005,
        COMPLETIONOVERRUN = 0x80000006,
        CONFERENCEFULL = 0x80000007,
        DIALBILLING = 0x80000008,
        DIALDIALTONE = 0x80000009,
        DIALPROMPT = 0x8000000A,
        DIALQUIET = 0x8000000B,
        INCOMPATIBLEAPIVERSION = 0x8000000C,
        INCOMPATIBLEEXTVERSION = 0x8000000D,
        INIFILECORRUPT = 0x8000000E,
        INUSE = 0x8000000F,
        INVALADDRESS = 0x80000010,
        INVALADDRESSID = 0x80000011,
        INVALADDRESSMODE = 0x80000012,
        INVALADDRESSSTATE = 0x80000013,
        INVALAPPHANDLE = 0x80000014,
        INVALAPPNAME = 0x80000015,
        INVALBEARERMODE = 0x80000016,
        INVALCALLCOMPLMODE = 0x80000017,
        INVALCALLHANDLE = 0x80000018,
        INVALCALLPARAMS = 0x80000019,
        INVALCALLPRIVILEGE = 0x8000001A,
        INVALCALLSELECT = 0x8000001B,
        INVALCALLSTATE = 0x8000001C,
        INVALCALLSTATELIST = 0x8000001D,
        INVALCARD = 0x8000001E,
        INVALCOMPLETIONID = 0x8000001F,
        INVALCONFCALLHANDLE = 0x80000020,
        INVALCONSULTCALLHANDLE = 0x80000021,
        INVALCOUNTRYCODE = 0x80000022,
        INVALDEVICECLASS = 0x80000023,
        INVALDEVICEHANDLE = 0x80000024,
        INVALDIALPARAMS = 0x80000025,
        INVALDIGITLIST = 0x80000026,
        INVALDIGITMODE = 0x80000027,
        INVALDIGITS = 0x80000028,
        INVALEXTVERSION = 0x80000029,
        INVALGROUPID = 0x8000002A,
        INVALLINEHANDLE = 0x8000002B,
        INVALLINESTATE = 0x8000002C,
        INVALLOCATION = 0x8000002D,
        INVALMEDIALIST = 0x8000002E,
        INVALMEDIAMODE = 0x8000002F,
        INVALMESSAGEID = 0x80000030,
        INVALPARAM = 0x80000032,
        INVALPARKID = 0x80000033,
        INVALPARKMODE = 0x80000034,
        INVALPOINTER = 0x80000035,
        INVALPRIVSELECT = 0x80000036,
        INVALRATE = 0x80000037,
        INVALREQUESTMODE = 0x80000038,
        INVALTERMINALID = 0x80000039,
        INVALTERMINALMODE = 0x8000003A,
        INVALTIMEOUT = 0x8000003B,
        INVALTONE = 0x8000003C,
        INVALTONELIST = 0x8000003D,
        INVALTONEMODE = 0x8000003E,
        INVALTRANSFERMODE = 0x8000003F,
        LINEMAPPERFAILED = 0x80000040,
        NOCONFERENCE = 0x80000041,
        NODEVICE = 0x80000042,
        NODRIVER = 0x80000043,
        NOMEM = 0x80000044,
        NOREQUEST = 0x80000045,
        NOTOWNER = 0x80000046,
        NOTREGISTERED = 0x80000047,
        OPERATIONFAILED = 0x80000048,
        OPERATIONUNAVAIL = 0x80000049,
        RATEUNAVAIL = 0x8000004A,
        RESOURCEUNAVAIL = 0x8000004B,
        REQUESTOVERRUN = 0x8000004C,
        STRUCTURETOOSMALL = 0x8000004D,
        TARGETNOTFOUND = 0x8000004E,
        TARGETSELF = 0x8000004F,
        UNINITIALIZED = 0x80000050,
        USERUSERINFOTOOBIG = 0x80000051,
        REINIT = 0x80000052,
        ADDRESSBLOCKED = 0x80000053,
        BILLINGREJECTED = 0x80000054,
        INVALFEATURE = 0x80000055,
        NOMULTIPLEINSTANCE = 0x80000056,

        INVALAGENTID = 0x80000057,      // TAPI v2.0
        INVALAGENTGROUP = 0x80000058,      // TAPI v2.0
        INVALPASSWORD = 0x80000059,      // TAPI v2.0
        INVALAGENTSTATE = 0x8000005A,      // TAPI v2.0
        INVALAGENTACTIVITY = 0x8000005B,      // TAPI v2.0
        DIALVOICEDETECT = 0x8000005C,      // TAPI v2.0

        // ExTAPI LINEERR_ constants
        INCORRECTPASSWORD = 0x80010001,
    }

    [Flags]
    public enum LINEDISCONNECTMODE
    {
        NORMAL = 0x00000001,
        UNKNOWN = 0x00000002,
        REJECT = 0x00000004,
        PICKUP = 0x00000008,
        FORWARDED = 0x00000010,
        BUSY = 0x00000020,
        NOANSWER = 0x00000040,
        BADADDRESS = 0x00000080,
        UNREACHABLE = 0x00000100,
        CONGESTION = 0x00000200,
        INCOMPATIBLE = 0x00000400,
        UNAVAIL = 0x00000800,
        NODIALTONE = 0x00001000,      // TAPI v1.4

        NUMBERCHANGED = 0x00002000,      // TAPI v2.0
        OUTOFORDER = 0x00004000,      // TAPI v2.0
        TEMPFAILURE = 0x00008000,      // TAPI v2.0
        QOSUNAVAIL = 0x00010000,      // TAPI v2.0
        BLOCKED = 0x00020000,      // TAPI v2.0
        DONOTDISTURB = 0x00040000,      // TAPI v2.0
        CANCELLED = 0x00080000,      // TAPI v2.0
        PHONECONNECTIONFAILURE = (LINEDISCONNECTMODE.NORMAL | (0xd0 << 16)),
        INVALIDSIMCARD = (LINEDISCONNECTMODE.NORMAL | (0xd1 << 16)),
        SIMCARDBUSY = (LINEDISCONNECTMODE.NORMAL | (0xd2 << 16)),
        NETWORKSERVICENOTAVAILABLE = (LINEDISCONNECTMODE.NORMAL | (0xd3 << 16)),
        EMERGENCYONLY = (LINEDISCONNECTMODE.NORMAL | (0xd4 << 16)),
    }

    public enum LINEMESSAGES
    {
        LINE_ADDRESSSTATE = 0,
        LINE_CALLINFO = 1,
        LINE_CALLSTATE = 2,
        LINE_CLOSE = 3,
        LINE_DEVSPECIFIC = 4,
        LINE_DEVSPECIFICFEATURE = 5,
        LINE_GATHERDIGITS = 6,
        LINE_GENERATE = 7,
        LINE_LINEDEVSTATE = 8,
        LINE_MONITORDIGITS = 9,
        LINE_MONITORMEDIA = 10,
        LINE_MONITORTONE = 11,
        LINE_REPLY = 12,
        LINE_REQUEST = 13,
        PHONE_BUTTON = 14,
        PHONE_CLOSE = 15,
        PHONE_DEVSPECIFIC = 16,
        PHONE_REPLY = 17,
        PHONE_STATE = 18,
        LINE_CREATE = 19,             // TAPI v1.4
        PHONE_CREATE = 20,             // TAPI v1.4

        LINE_AGENTSPECIFIC = 21,             // TAPI v2.0
        LINE_AGENTSTATUS = 22,             // TAPI v2.0
        LINE_APPNEWCALL = 23,             // TAPI v2.0
        LINE_PROXYREQUEST = 24,             // TAPI v2.0
        LINE_REMOVE = 25,             // TAPI v2.0
        PHONE_REMOVE = 26,             // TAPI v2.0
    }

    [Flags]
    public enum LINEADDRCAPFLAGS
    {
        FWDNUMRINGS = 0x00000001,
        PICKUPGROUPID = 0x00000002,
        SECURE = 0x00000004,
        BLOCKIDDEFAULT = 0x00000008,
        BLOCKIDOVERRIDE = 0x00000010,
        DIALED = 0x00000020,
        ORIGOFFHOOK = 0x00000040,
        DESTOFFHOOK = 0x00000080,
        FWDCONSULT = 0x00000100,
        SETUPCONFNULL = 0x00000200,
        AUTORECONNECT = 0x00000400,
        COMPLETIONID = 0x00000800,
        TRANSFERHELD = 0x00001000,
        TRANSFERMAKE = 0x00002000,
        CONFERENCEHELD = 0x00004000,
        CONFERENCEMAKE = 0x00008000,
        PARTIALDIAL = 0x00010000,
        FWDSTATUSVALID = 0x00020000,
        FWDINTEXTADDR = 0x00040000,
        FWDBUSYNAADDR = 0x00080000,
        ACCEPTTOALERT = 0x00100000,
        CONFDROP = 0x00200000,
        PICKUPCALLWAIT = 0x00400000,

        PREDICTIVEDIALER = 0x00800000,      // TAPI v2.0
        QUEUE = 0x01000000,      // TAPI v2.0
        ROUTEPOINT = 0x02000000,      // TAPI v2.0
        HOLDMAKESNEW = 0x04000000,      // TAPI v2.0
        NOINTERNALCALLS = 0x08000000,      // TAPI v2.0
        NOEXTERNALCALLS = 0x10000000,      // TAPI v2.0
        SETCALLINGID = 0x20000000,      // TAPI v2.0
    }

    [Flags]
    public enum LINEBEARERMODE
    {
        VOICE = 0x00000001,
        SPEECH = 0x00000002,
        MULTIUSE = 0x00000004,
        DATA = 0x00000008,
        ALTSPEECHDATA = 0x00000010,
        NONCALLSIGNALING = 0x00000020,
        PASSTHROUGH = 0x00000040,      // TAPI v1.4
    }

    public enum LINECALLSELECT
    {
        LINE = 0x00000001,
        ADDRESS = 0x00000002,
        CALL = 0x00000004,
        DEVICEID = 0x00000008,      // TAPI v2.1
        CALLID = 0x00000010,      // TAPI v3.0
    }

    [Flags]
    public enum LINEADDRESSMODE
    {
        ADDRESSID = 0x00000001,
        DIALABLEADDR = 0x00000002,
    }

    [Flags]
    public enum LINECALLINFOSTATE
    {
        OTHER = 0x00000001,
        DEVSPECIFIC = 0x00000002,
        BEARERMODE = 0x00000004,
        RATE = 0x00000008,
        MEDIAMODE = 0x00000010,
        APPSPECIFIC = 0x00000020,
        CALLID = 0x00000040,
        RELATEDCALLID = 0x00000080,
        ORIGIN = 0x00000100,
        REASON = 0x00000200,
        COMPLETIONID = 0x00000400,
        NUMOWNERINCR = 0x00000800,
        NUMOWNERDECR = 0x00001000,
        NUMMONITORS = 0x00002000,
        TRUNK = 0x00004000,
        CALLERID = 0x00008000,
        CALLEDID = 0x00010000,
        CONNECTEDID = 0x00020000,
        REDIRECTIONID = 0x00040000,
        REDIRECTINGID = 0x00080000,
        DISPLAY = 0x00100000,
        USERUSERINFO = 0x00200000,
        HIGHLEVELCOMP = 0x00400000,
        LOWLEVELCOMP = 0x00800000,
        CHARGINGINFO = 0x01000000,
        TERMINAL = 0x02000000,
        DIALPARAMS = 0x04000000,
        MONITORMODES = 0x08000000,

        TREATMENT = 0x10000000,      // TAPI v2.0
        QOS = 0x20000000,      // TAPI v2.0
        CALLDATA = 0x40000000,      // TAPI v2.0
    }

    [Flags]
    public enum LINECALLSTATE
    {
        IDLE = 0x00000001,
        OFFERING = 0x00000002,
        ACCEPTED = 0x00000004,
        DIALTONE = 0x00000008,
        DIALING = 0x00000010,
        RINGBACK = 0x00000020,
        BUSY = 0x00000040,
        SPECIALINFO = 0x00000080,
        CONNECTED = 0x00000100,
        PROCEEDING = 0x00000200,
        ONHOLD = 0x00000400,
        CONFERENCED = 0x00000800,
        ONHOLDPENDCONF = 0x00001000,
        ONHOLDPENDTRANSFER = 0x00002000,
        DISCONNECTED = 0x00004000,
        UNKNOWN = 0x00008000,
    }

    [Flags]
    public enum LINEDEVSTATE
    {
        OTHER = 0x00000001,
        RINGING = 0x00000002,
        CONNECTED = 0x00000004,
        DISCONNECTED = 0x00000008,
        MSGWAITON = 0x00000010,
        MSGWAITOFF = 0x00000020,
        INSERVICE = 0x00000040,
        OUTOFSERVICE = 0x00000080,
        MAINTENANCE = 0x00000100,
        OPEN = 0x00000200,
        CLOSE = 0x00000400,
        NUMCALLS = 0x00000800,
        NUMCOMPLETIONS = 0x00001000,
        TERMINALS = 0x00002000,
        ROAMMODE = 0x00004000,
        BATTERY = 0x00008000,
        SIGNAL = 0x00010000,
        DEVSPECIFIC = 0x00020000,
        REINIT = 0x00040000,
        LOCK = 0x00080000,
        CAPSCHANGE = 0x00100000,      // TAPI v1.4
        CONFIGCHANGE = 0x00200000,      // TAPI v1.4
        TRANSLATECHANGE = 0x00400000,      // TAPI v1.4
        COMPLCANCEL = 0x00800000,      // TAPI v1.4
        REMOVED = 0x01000000,      // TAPI v1.4
    }

    [Flags]
    public enum LINEDEVCAPFLAGS
    {
        CROSSADDRCONF = 0x00000001,
        HIGHLEVCOMP = 0x00000002,
        LOWLEVCOMP = 0x00000004,
        MEDIACONTROL = 0x00000008,
        MULTIPLEADDR = 0x00000010,
        CLOSEDROP = 0x00000020,
        DIALBILLING = 0x00000040,
        DIALQUIET = 0x00000080,
        DIALDIALTONE = 0x00000100,
        MSP = 0x00000200,      // TAPI v3.0
        CALLHUB = 0x00000400,      // TAPI v3.0
        CALLHUBTRACKING = 0x00000800,      // TAPI v3.0
        PRIVATEOBJECTS = 0x00001000,      // TAPI v3.0
    }

    [Flags]
    public enum LINEANSWERMODE
    {
        NONE = 0x00000001,
        DROP = 0x00000002,
        HOLD = 0x00000004,
    }

    [Flags]
    public enum LINECALLPRIVILEGE
    {
        NONE = 0x00000001,
        MONITOR = 0x00000002,
        OWNER = 0x00000004,
    }

    [Flags]
    public enum LINEDIGITMODE
    {
        PULSE = 0x00000001,
        DTMF = 0x00000002,
        DTMFEND = 0x00000004,
    }

    public enum CALLER_ID_OPTIONS
    {
        DEFAULT,  /* Accept the default behavior */
        BLOCK,    /* Block sending of caller-ID information, overriding the current default if necessary */
        PRESENT,  /* Send caller-ID information, overriding the current default if necessary */
    }

    [Flags]
    public enum LINECALLORIGIN
    {
        OUTBOUND = 0x00000001,
        INTERNAL = 0x00000002,
        EXTERNAL = 0x00000004,
        UNKNOWN = 0x00000010,
        UNAVAIL = 0x00000020,
        CONFERENCE = 0x00000040,
        INBOUND = 0x00000080,      // TAPI v1.4
    }

    [Flags]
    public enum LINECALLPARAMFLAGS
    {
        SECURE = 0x00000001,
        IDLE = 0x00000002,
        BLOCKID = 0x00000004,
        ORIGOFFHOOK = 0x00000008,
        DESTOFFHOOK = 0x00000010,

        NOHOLDCONFERENCE = 0x00000020,      // TAPI v2.0
        PREDICTIVEDIAL = 0x00000040,      // TAPI v2.0
        ONESTEPTRANSFER = 0x00000080,      // TAPI v2.0
    }

    [Flags]
    public enum LINEDIALTONEMODE
    {
        NORMAL = 0x00000001,
        SPECIAL = 0x00000002,
        INTERNAL = 0x00000004,
        EXTERNAL = 0x00000008,
        UNKNOWN = 0x00000010,
        UNAVAIL = 0x00000020,
    }

    [Flags]
    public enum LINECALLREASON
    {
        DIRECT = 0x00000001,
        FWDBUSY = 0x00000002,
        FWDNOANSWER = 0x00000004,
        FWDUNCOND = 0x00000008,
        PICKUP = 0x00000010,
        UNPARK = 0x00000020,
        REDIRECT = 0x00000040,
        CALLCOMPLETION = 0x00000080,
        TRANSFER = 0x00000100,
        REMINDER = 0x00000200,
        UNKNOWN = 0x00000400,
        UNAVAIL = 0x00000800,
        INTRUDE = 0x00001000,      // TAPI v1.4
        PARKED = 0x00002000,      // TAPI v1.4

        CAMPEDON = 0x00004000,      // TAPI v2.0
        ROUTEREQUEST = 0x00008000,      // TAPI v2.0
    }

    [Flags]
    public enum LINEFEATURE
    {
        DEVSPECIFIC = 0x00000001,
        DEVSPECIFICFEAT = 0x00000002,
        FORWARD = 0x00000004,
        MAKECALL = 0x00000008,
        SETMEDIACONTROL = 0x00000010,
        SETTERMINAL = 0x00000020,

        SETDEVSTATUS = 0x00000040,      // TAPI v2.0
        FORWARDFWD = 0x00000080,      // TAPI v2.0
        FORWARDDND = 0x00000100,      // TAPI v2.0
    }

    [Flags]
    public enum LINEROAMMODE
    {
        UNKNOWN = 0x00000001,
        UNAVAIL = 0x00000002,
        HOME = 0x00000004,
        ROAMA = 0x00000008,
        ROAMB = 0x00000010,
    }

    [Flags]
    public enum LINEDEVSTATUSFLAGS
    {
        CONNECTED = 0x00000001,
        MSGWAIT = 0x00000002,
        INSERVICE = 0x00000004,
        LOCKED = 0x00000008,
    }

    [Flags]
    public enum LINEFORWARDMODE
    {
        UNCOND = 0x00000001,
        UNCONDINTERNAL = 0x00000002,
        UNCONDEXTERNAL = 0x00000004,
        UNCONDSPECIFIC = 0x00000008,
        BUSY = 0x00000010,
        BUSYINTERNAL = 0x00000020,
        BUSYEXTERNAL = 0x00000040,
        BUSYSPECIFIC = 0x00000080,
        NOANSW = 0x00000100,
        NOANSWINTERNAL = 0x00000200,
        NOANSWEXTERNAL = 0x00000400,
        NOANSWSPECIFIC = 0x00000800,
        BUSYNA = 0x00001000,
        BUSYNAINTERNAL = 0x00002000,
        BUSYNAEXTERNAL = 0x00004000,
        BUSYNASPECIFIC = 0x00008000,
        UNKNOWN = 0x00010000,      // TAPI v1.4
        UNAVAIL = 0x00020000,      // TAPI v1.4
    }

    [Flags]
    public enum LINEADDRESSSTATE
    {
        OTHER = 0x00000001,
        DEVSPECIFIC = 0x00000002,
        INUSEZERO = 0x00000004,
        INUSEONE = 0x00000008,
        INUSEMANY = 0x00000010,
        NUMCALLS = 0x00000020,
        FORWARD = 0x00000040,
        TERMINALS = 0x00000080,
        CAPSCHANGE = 0x00000100,      // TAPI v1.4
    }

    [Flags]
    public enum LINECALLFEATURE
    {
        LINECALLFEATURE_ACCEPT = 0x000000001, //Accept the call (lineAccept).  
        LINECALLFEATURE_ADDTOCONF = 0x00000002, //Add the call to the current conference (lineAddToConference).  
        LINECALLFEATURE_ANSWER = 0x00000004, //Answer the call (lineAnswer).  
        LINECALLFEATURE_BLINDTRANSFER = 0x00000008, //Perform a blind transfer on the call (lineBlindTransfer).  
        LINECALLFEATURE_COMPLETETRANSF = 0x00000020, //Complete the call transfer (lineCompleteTransfer).  
        LINECALLFEATURE_DIAL = 0x00000040, //Dial the destination number for the call (lineDial).  
        LINECALLFEATURE_DROP = 0x00000080, //Drop the call (lineDrop).  
        LINECALLFEATURE_GENERATEDIGITS = 0x00000200, //Generate digits on the call (lineGenerateDigits).  
        LINECALLFEATURE_GENERATETONE = 0x00000400, //Generate tones on the call (lineGenerateTone).  
        LINECALLFEATURE_HOLD = 0x00000800, //Put the call on hold (lineHold).  
        LINECALLFEATURE_MONITORDIGITS = 0x00001000, //Monitor digits on the call (lineMonitorDigits).  
        LINECALLFEATURE_MONITORMEDIA = 0x00002000, //Monitor the call's media (lineMonitorMedia).  
        LINECALLFEATURE_PREPAREADDCONF = 0x00010000, //Prepare the call for addition to a conference (linePrepareAddToConference).  
        LINECALLFEATURE_REDIRECT = 0x00020000, //Redirect the call to another destination (lineRedirect).  
        LINECALLFEATURE_RELEASEUSERUSERINFO = 0x10000000, //Release current user-user information (lineReleaseUserUserInfo). (TAPI version 1.4 and later.) 
        LINECALLFEATURE_REMOVEFROMCONF = 0x00040000, //Remove the call from the conference (lineRemoveFromConference).  
        LINECALLFEATURE_SENDUSERUSER = 0x00100000, //Send user-user information (lineSendUserUserInfo).  
        LINECALLFEATURE_SETCALLPARAMS = 0x00200000, //Set call parameters (lineSetCallParams)  
        LINECALLFEATURE_SETQOS = 0x40000000, //Set QOS levels for the call. TAPI version 2.0 and later. 
        LINECALLFEATURE_SETTERMINAL = 0x00800000, //Set the terminal to be used with the call (lineSetTerminal).  
        LINECALLFEATURE_SETUPCONF = 0x01000000, //Set up a conference (lineSetupConference).  
        LINECALLFEATURE_SETTREATMENT = 0x20000000, //Set call treatment. TAPI version 2.0 and later. 
        LINECALLFEATURE_SETUPTRANSFER = 0x02000000, //Set up a transfer (lineSetupTransfer).  
        LINECALLFEATURE_SWAPHOLD = 0x04000000, //Perform a swap hold operation (lineSwapHold).  
        LINECALLFEATURE_UNHOLD = 0x08000000,
    }

    [Flags]
    public enum LINECALLFEATURE2
    {
        LINECALLFEATURE2_NOHOLDCONFERENCE = 0x00000001, // If this bit is on, a "no hold conference" can be created by using the LINECALLPARAMFLAGS_NOHOLDCONFERENCE option with lineSetupConference. The LINECALLFEATURE_SETUPCONF bit will also be on in the dwCallFeatures member in the LINECALLSTATUS structure. 
        LINECALLFEATURE2_ONESTEPTRANSFER = 0x00000002,	// If this bit is on, "one step transfer" can be created by using the LINECALLPARAMFLAGS_ONESTEPTRANSFER option with lineSetupTransfer. The LINECALLFEATURE_SETUPTRANSFER bit will also be on in the dwCallFeatures member.  
        LINECALLFEATURE2_TRANSFERCONF = 0x00000080,		// If this bit is on, the lineCompleteTransfer function can be used to resolve the transfer as a three-way conference. The LINECALLFEATURE_COMPLETETRANSF bit will also be on in the dwCallFeatures member. 
        LINECALLFEATURE2_TRANSFERNORM = 0x00000040,		// If this bit is on, the lineCompleteTransfer function can be used to resolve the transfer as a normal transfer. The LINECALLFEATURE_COMPLETETRANSF bit will also be on in the dwCallFeatures member.  
    }



}


