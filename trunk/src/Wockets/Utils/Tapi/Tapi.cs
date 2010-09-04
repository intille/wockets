using System;
using System.Threading;
using System.Text;
using System.Collections;
using System.Reflection;
using System.Runtime.InteropServices;
using System.IO;
using System.Windows.Forms;

namespace Wockets.Utils.Tapi
{
    /// <summary>
    /// General TAPI wrapper class
    /// </summary>
    public class Tapi
    {
        #region Internal data
        private IntPtr m_hLineApp;
        private int dwNumDev;
        private IntPtr hEvent = IntPtr.Zero; // Not currently used
        private Thread thTapi;

        /// <summary>
        /// Collection of open TAPI lines
        /// </summary>
        internal Hashtable Lines;
        /// <summary>
        /// Collection of active TAPI calls
        /// </summary>
        internal Hashtable Calls;
        /// <summary>
        /// Collection of pending TAPI asynchronous requests
        /// </summary>
        internal Hashtable PendingRequests;
        #endregion

        #region Public data
        /// <summary>
        /// Minimum suported API version. Set this before call to Initialize if needed
        /// </summary>
        public int dwAPIVersionLow = 0x10004;
        /// <summary>
        /// Maximum suported API version. Set this before call to Initialize if needed
        /// </summary>
        public int dwAPIVersionHigh = 0x20000;
        /// <summary>
        /// Number of devices registered with TAPI
        /// </summary>
        /// <value>int</value>
        public int NumDevices { get { return dwNumDev; } }
        /// <summary>
        /// TAPI HLINEAPP
        /// </summary>
        /// <value></value>
        public IntPtr hLineApp { get { return m_hLineApp; } }
        #endregion

        #region Delegate definitions
        /// <summary>
        /// </summary>
        public delegate void ReinitializeHandler();
        /// <summary>
        /// </summary>
        public delegate void MessageHandler(LINEMESSAGE msg);
        #endregion

        #region Events
        /// <summary>
        /// Invoked when LINE_REINIT is received
        /// </summary>
        public event ReinitializeHandler Reinitialize;
        /// <summary>
        /// Invoked when TAPI message is received, but before it is processed
        /// </summary>
        public event MessageHandler LineMessage;
        #endregion

        /// <summary>
        /// Constructor. Creates an instance of Tapi object
        /// </summary>
        public Tapi()
        {
            Lines = new Hashtable();
            Calls = new Hashtable();

            PendingRequests = new Hashtable();
        }

        /// <summary>
        /// Intialize TAPI data. Throws a TapiException if unsuccessful
        /// </summary>
        /// <returns>returns result of the call to lineInitializeEx</returns>
        public int Initialize()
        {
            // We support API version up to 2.0
            int dwApiVersion = 0x20000;
            LINEINITIALIZEEXPARAMS initParams = new LINEINITIALIZEEXPARAMS(hEvent);

            // Intialize TAPI app and throw an exception if failed
            int ret = NativeTapi.lineInitializeEx(out m_hLineApp, IntPtr.Zero, IntPtr.Zero, "MyApp", out dwNumDev, ref dwApiVersion, initParams);
            if (ret != 0)
                throw new TapiException(ret);

            // Start listen for events
            thTapi = new Thread(new ThreadStart(TapiThreadProc));
            thTapi.Start();

            //TODO: build device list

            return ret;
        }


        /// <summary>
        /// Stop all TAPI related activity. Perform cleanup
        /// </summary>
        public void Shutdown()
        {
            // Destroy active calls if any
            object[] arr = new object[Calls.Values.Count];
            Calls.Values.CopyTo(arr, 0);
            foreach (Call call in arr)
                call.Dispose();

            // Close lines
            arr = new object[Lines.Values.Count];
            Lines.Values.CopyTo(arr, 0);
            foreach (Line line in arr)
                line.Dispose();

            // Even though this flag is set to false, event thread will keep waiting indefinitely inside the call
            // to lineGetMessage. Calling lineShutdown will result in LINE_CLOSE being sent and thread successfully 
            // terminated
            stop = true;
            NativeTapi.lineShutdown(m_hLineApp);
        }

        /// <summary>
        /// Opens TAPI line
        /// </summary>
        /// <param name="deviceID">ID of the device to open. Must be less than <c>NumDevices</c></param>
        /// <param name="mode">combination of <c>LINEMEDIAMODE</c> flags</param>
        /// <param name="priv">combination of <c>LINECALLPRIVILEGE</c> flags</param>
        /// <returns>Newly created Line object</returns>
        public Line CreateLine(int deviceID, LINEMEDIAMODE mode, LINECALLPRIVILEGE priv)
        {
            IntPtr hLine;
            int ret = NativeTapi.lineOpen(m_hLineApp, deviceID, out hLine, NegotiateVersion(deviceID), 0, IntPtr.Zero, priv, mode, IntPtr.Zero);
            if (ret != 0)
                throw new TapiException(ret);
            Line line = new Line(this, hLine);
            Lines.Add(hLine, line);
            return line;
        }

        /// <summary>
        /// Retrieves device caps
        /// </summary>
        /// <param name="deviceID">ID of the device. Must be less than <c>NumDevices</c></param>
        /// <returns>Filled-in LINEDEVCAPS structure</returns>
        public LINEERR GetDevCaps(int deviceID, out LINEDEVCAPS dc)
        {
            dc = new LINEDEVCAPS(1024);
            dc.Store();
            int ret = NativeTapi.lineGetDevCaps(m_hLineApp, deviceID, NegotiateVersion(deviceID), 0, dc.Data);
            dc.Load();
            if ((LINEERR)ret == LINEERR.STRUCTURETOOSMALL)
            {
                dc = new LINEDEVCAPS(dc.dwNeededSize);
                ret = NativeTapi.lineGetDevCaps(m_hLineApp, deviceID, NegotiateVersion(deviceID), 0, dc.Data);
                dc.Load();
            }
            return (LINEERR)ret;
        }

        /// <summary>
        /// Negotiates API version with TAPI for a given device
        /// </summary>
        /// <param name="deviceID">ID of the device. Must be less than <c>NumDevices</c></param>
        /// <returns>Negotiated API version</returns>
        public int NegotiateVersion(int deviceID)
        {
            int dwApiVersion;
            LINEEXTENSIONID le;
            int ret = NativeTapi.lineNegotiateAPIVersion(m_hLineApp, deviceID, dwAPIVersionLow, dwAPIVersionHigh, out dwApiVersion, out le);
            if (ret != 0)
                throw new TapiException(ret);
            return dwApiVersion;
        }

        protected void OnMessage(LINEMESSAGE msg)
        {
            if (LineMessage != null)
                LineMessage(msg);
        }

        protected void OnLineReinit()
        {
            Shutdown();
            Lines.Clear();
            Calls.Clear();
            PendingRequests.Clear();
            Initialize();
            if (Reinitialize != null)
                Reinitialize();
        }

        protected void OnLineClose(LINEMESSAGE msg)
        {
            IntPtr hLine = msg.hDevice;
            Line line = Lines[hLine] as Line;
            if (line != null)
                line.Dispose();
        }

        protected void OnLineReply(LINEMESSAGE msg)
        {
            lock (PendingRequests.SyncRoot)
            {
                object ar = PendingRequests[(int)msg.dwParam1];
                if (ar != null)
                {
                    if (ar is MakeCallAsyncResult)
                    {
                        ((ar as MakeCallAsyncResult).AsyncWaitHandle as ManualResetEvent).Set();
                        if ((ar as MakeCallAsyncResult).Callback != null)
                            (ar as MakeCallAsyncResult).Callback(ar as IAsyncResult);
                    }
                    PendingRequests.Remove((int)msg.dwParam1);
                }
            }
        }


        /// <summary>
        /// Main event-listening loop
        /// </summary>
        private bool stop = false;
        private void TapiThreadProc()
        {
            while (!stop)
            {
                LINEMESSAGE msg;
                if (NativeTapi.lineGetMessage(m_hLineApp, out msg, -1) == 0)
                {
                    OnMessage(msg);

                    switch (msg.dwMessageID)
                    {
                        case LINEMESSAGES.LINE_CLOSE:
                            OnLineClose(msg);
                            break;

                        case LINEMESSAGES.LINE_CALLINFO:
                            OnLineCallInfo(msg);
                            break;
                        case LINEMESSAGES.LINE_CALLSTATE:
                            OnLineCallState(msg);
                            break;
                        case LINEMESSAGES.LINE_REPLY:
                            OnLineReply(msg);
                            break;
                        case LINEMESSAGES.LINE_APPNEWCALL:
                            OnNewCall(msg);
                            break;
                    }
                }
            }
        }

        private void OnNewCall(LINEMESSAGE msg)
        {
            bool bNewCall = false;

            if (!Calls.Contains(msg.dwParam2))
            {
                Calls.Add(msg.dwParam2, new Call(msg.dwParam2));
                bNewCall = true;
            }

            if (Calls.Contains(msg.dwParam2))
            {
                Call call = Calls[msg.dwParam2] as Call;
                call.m_addressID = msg.dwParam1.ToInt32();

                if (call.m_line == null)
                {
                    Line line = Lines[msg.hDevice] as Line;

                    call.m_line = line;
                    if (bNewCall && line != null)
                        line.OnNewCall(call);
                }
            }
        }

        private void OnLineCallInfo(LINEMESSAGE msg)
        {
            bool bNewCall = false;

            if (!Calls.Contains(msg.hDevice))
            {
                Calls.Add(msg.hDevice, new Call(msg.hDevice));
                bNewCall = true;
            }

            if (Calls.Contains(msg.hDevice))
            {
                Call call = Calls[msg.hDevice] as Call;

                call.OnLineCallInfo(msg);
                if (call.m_line == null)
                {
                    Line line = Lines[call.Info.hLine] as Line;

                    call.m_line = line;
                    if (bNewCall && line != null)
                        line.OnNewCall(call);
                }
            }
        }

        private void OnLineCallState(LINEMESSAGE msg)
        {
            bool bNewCall = false;

            if (!Calls.Contains(msg.hDevice))
            {
                Calls.Add(msg.hDevice, new Call(msg.hDevice));
                bNewCall = true;
            }

            if (Calls.Contains(msg.hDevice))
            {
                Call call = Calls[msg.hDevice] as Call;

                call.OnLineCallState(msg);
                if (bNewCall)
                {
                    call.LoadCallInfo();

                    Line line = Lines[call.Info.hLine] as Line;

                    call.m_line = line;
                    if (line != null)
                        line.OnNewCall(call);
                }
            }
        }
    }


    /// <summary>
    /// Wrapper class for TAPI line
    /// </summary>
    public class Line : IDisposable
    {
        private Tapi tapi;
        private IntPtr m_hLine;
        private bool bSyncMakeCall = false;

        /// <summary>
        /// TAPI HLINE accessor
        /// </summary>
        public IntPtr hLine { get { return m_hLine; } }

        public delegate void NewCallHandler(Call call);
        public event NewCallHandler NewCall;

        internal Line(Tapi t, IntPtr hLine)
        {
            tapi = t;
            this.m_hLine = hLine;
        }

        /// <summary>
        /// Asynchronous function to place a call
        /// </summary>
        /// <param name="Destination">String: phone number</param>
        /// <param name="CountryCode">int: country code, e.g. 1 for US</param>
        /// <param name="Params"><c>LINECALLPARAMS</c> structure data</param>
        /// <param name="Callback">Asynchronous callback. Will be invoked when the call is complete</param>
        /// <param name="State">User-defined state object. Can be null</param>
        /// <returns>IAsyncResult</returns>
        public IAsyncResult BeginMakeCall(string Destination, int CountryCode, /*LINECALLPARAMS*/ byte[] Params, AsyncCallback Callback, object State)
        {
            bSyncMakeCall = false;
            MakeCallAsyncResult result = new MakeCallAsyncResult(0, Callback, State);

            lock (tapi.PendingRequests.SyncRoot)
            {
                int ret = NativeTapi.lineMakeCall(m_hLine, out result.m_hCall, Destination, CountryCode, Params);
                result.ReplyID = ret;
                if (ret > 0)
                    tapi.PendingRequests.Add(ret, result);
            }
            return result;
        }

        /// <summary>
        /// BeginMakeCall counterpart
        /// </summary>
        /// <param name="ar">IAsyncResult returned by <c>BeginMakeCall</c></param>
        /// <returns>New Call object, or null if failed</returns>
        public Call EndMakeCall(IAsyncResult ar)
        {
            MakeCallAsyncResult mc = ar as MakeCallAsyncResult;
            if (mc == null)
                throw new ArgumentException("Invalid parameter", "ar");
            if (!mc.IsCompleted)
                mc.AsyncWaitHandle.WaitOne();
            Call call = tapi.Calls[mc.hCall] as Call;
            if (call == null)
            {
                call = new Call(mc.m_hCall);
                tapi.Calls.Add(mc.m_hCall, call);
                call.LoadCallInfo();
                call.LoadCallState();
                //				call.OnLineCallInfo(
                //				LINECALLINFO lci = new LINECALLINFO(1024);
                //				lci.Store();
                //				int ret = NativeTapi.lineGetCallInfo(mc.m_hCall, lci.Data);
                //				if (ret >= 0)
                //				{
                //					lci.Load();
                //					call.m_line = tapi.Lines[lci.hLine] as Line;
                //				}
            }
            return call;
        }

        public Call MakeCall(string Destination, int CountryCode, bool SupressCallerID)
        {
            byte[] Params = null;
            if (SupressCallerID)
            {
                // If we want to supress caller ID, we need to prepare LINECALLPARAMS
                LINECALLPARAMS lp = new LINECALLPARAMS(Marshal.SizeOf(typeof(LINECALLPARAMS)) + Marshal.SizeOf(typeof(LINECALLPARAMSDEVSPECIFIC)));
                lp.dwDevSpecificOffset = Marshal.SizeOf(typeof(LINECALLPARAMS));
                lp.dwDevSpecificSize = Marshal.SizeOf(typeof(LINECALLPARAMSDEVSPECIFIC));
                lp.Store();
                LINECALLPARAMSDEVSPECIFIC lcpds = new LINECALLPARAMSDEVSPECIFIC();
                lcpds.cidoOptions = CALLER_ID_OPTIONS.BLOCK;
                int index = lp.dwDevSpecificOffset;
                ByteCopy.StructToByteArray(lcpds, ref index, lp.Data);
                Params = lp.Data;
            }
            return MakeCall(Destination, CountryCode, Params);
        }

        public Call MakeCall(string Destination, int CountryCode, /*LINECALLPARAMS*/ byte[] Params)
        {
            IAsyncResult ar = BeginMakeCall(Destination, CountryCode, Params, null, null);
            bSyncMakeCall = true;
            MakeCallAsyncResult mc = ar as MakeCallAsyncResult;
            bool bDone = false;
            while (!bDone)
            {
                Monitor.Enter(mc);
                if (mc.IsCompleted)
                    bDone = true;
                Monitor.Exit(mc);
                Application.DoEvents();
            }
            //			if ( !(ar as MakeCallAsyncResult).IsCompleted )
            //				ar.AsyncWaitHandle.WaitOne();
            Call call = EndMakeCall(ar);
            return call;
        }

        internal void MakeCallCallback(IAsyncResult ar)
        {
        }

        internal protected void OnNewCall(Call call)
        {
            if (NewCall != null && !bSyncMakeCall)
                NewCall(call);
        }

        #region IDisposable Members

        /// <summary>
        /// Cleanup
        /// </summary>
        public void Dispose()
        {
            NativeTapi.lineClose(hLine);
            if (tapi.Lines.Contains(hLine))
                tapi.Lines.Remove(hLine);
        }

        #endregion
    }


    /// <summary>
    /// TAPI call wrapper
    /// </summary>
    public class Call : IDisposable
    {
        private IntPtr m_hCall;
        private LINECALLSTATE m_state;
        private LINECALLINFO m_info;
        private string m_callerID = "";
        internal int m_addressID;
        internal Line m_line;

        internal Call(IntPtr hCall)
        {
            m_hCall = hCall;
            m_info = new LINECALLINFO(Marshal.SizeOf(typeof(LINECALLINFO)));
        }

        public void Hangup()
        {
            NativeTapi.lineDrop(m_hCall, null, 0);
        }

        public LINECALLSTATE State { get { return m_state; } }
        public LINECALLINFO Info { get { return m_info; } }
        public string CallerID { get { return m_callerID; } }
        public Line Line { get { return m_line; } }
        public int AddressID { get { return m_addressID; } }

        #region Delegate definitions
        public delegate void CallStateHandler(Call call, LINECALLSTATE state);
        public delegate void CallInfoHandler(Call call, LINECALLINFOSTATE infoState, LINECALLINFO info);
        #endregion

        #region Events
        public event CallInfoHandler CallInfo;
        public event CallStateHandler CallState;
        #endregion

        #region Event handlers
        protected internal void OnLineCallState(LINEMESSAGE msg)
        {
            m_state = (LINECALLSTATE)msg.dwParam1.ToInt32();
            if (CallState != null)
                CallState(this, m_state);
            //			if ( m_state == LINECALLSTATE.LINECALLSTATE_IDLE )
            //				Dispose();
        }

        protected internal void OnLineCallInfo(LINEMESSAGE msg)
        {
            LINECALLINFOSTATE infoState = (LINECALLINFOSTATE)msg.dwParam1.ToInt32();
            LoadCallInfo();
            if ((infoState & LINECALLINFOSTATE.CALLERID) == LINECALLINFOSTATE.CALLERID)
            {
                if (m_info.dwCallerIDSize != 0)
                    m_callerID = Encoding.Unicode.GetString(m_info.Data, m_info.dwCallerIDOffset, m_info.dwCallerIDSize - 1);
            }
            if (CallInfo != null)
                CallInfo(this, (LINECALLINFOSTATE)msg.dwParam1.ToInt32(), m_info);
        }

        protected internal void OnLineMonitorTones(LINEMESSAGE msg)
        {
        }

        #endregion

        protected internal void LoadCallInfo()
        {
            m_info = new LINECALLINFO(1024);
            m_info.Store();
            int ret = NativeTapi.lineGetCallInfo(m_hCall, m_info.Data); m_info.Load();
            if (ret < 0)
                throw new TapiException(ret);
        }

        protected internal void LoadCallState()
        {
            LINECALLSTATUS status = new LINECALLSTATUS(1024);
            status.Store();
            int ret = NativeTapi.lineGetCallStatus(m_hCall, status.Data);
            status.Load();
            if (ret < 0)
                throw new TapiException(ret);
            m_state = status.dwCallState;
        }

        #region IDisposable Members

        public void Dispose()
        {
            // TODO:  Add Call.Dispose implementation
        }

        #endregion

    }

    #region Async callback handling

    internal class TapiAsyncResult : IAsyncResult
    {
        protected int m_replyID;
        private AsyncCallback m_callback;
        private object m_state;
        private ManualResetEvent m_eventDone;

        internal int ReplyID { set { m_replyID = value; } get { return m_replyID; } }
        internal AsyncCallback Callback { get { return m_callback; } }

        internal TapiAsyncResult(int ReplyID, AsyncCallback callback, object State)
        {
            m_replyID = ReplyID;
            m_callback = callback;
            m_state = State;
        }

        #region IAsyncResult Members

        public object AsyncState
        {
            get
            {
                return m_state;
            }
        }

        public bool CompletedSynchronously
        {
            get
            {
                return m_replyID < 0;
            }
        }

        public WaitHandle AsyncWaitHandle
        {
            get
            {
                if (m_eventDone == null)
                    m_eventDone = new ManualResetEvent(false);
                return m_eventDone;
            }
        }

        public virtual bool IsCompleted
        {
            get
            {
                return false;
            }
        }

        #endregion

    }

    internal class MakeCallAsyncResult : TapiAsyncResult, IDisposable
    {
        internal IntPtr m_hCall;
        private GCHandle m_handle;
        internal MakeCallAsyncResult(int ReplyID, AsyncCallback callback, object State)
            : base(ReplyID, callback, State)
        {
            m_handle = GCHandle.Alloc(this, GCHandleType.Pinned);
        }

        internal IntPtr hCall { get { return m_hCall; } }

        public override bool IsCompleted
        {
            get
            {
                return m_hCall != IntPtr.Zero || ReplyID <= 0;
            }
        }


        #region IDisposable Members

        public void Dispose()
        {
            m_handle.Free();
        }

        #endregion
    }

    #endregion

    public class NativeTapi
    {
        [DllImport("coredll")]
        extern static public int lineInitializeEx(
            out IntPtr lpm_hLineApp,
            IntPtr hInstance,
            IntPtr lpfnCallback,
            string lpszFriendlyAppName,
            out int lpdwNumDevs,
            ref int lpdwAPIVersion,
            LINEINITIALIZEEXPARAMS lpLineInitializeExParams);

        [DllImport("coredll")]
        extern static public int lineOpen(IntPtr m_hLineApp,
            int dwDeviceID,
            out IntPtr lphLine,
            int dwAPIVersion,
            int dwExtVersion,
            IntPtr dwCallbackInstance,
            LINECALLPRIVILEGE dwPrivileges,
            LINEMEDIAMODE dwMediaModes,
            LINECALLPARAMS lpCallParams);

        [DllImport("coredll")]
        extern static public int lineOpen(IntPtr m_hLineApp,
            int dwDeviceID,
            out IntPtr lphLine,
            int dwAPIVersion,
            int dwExtVersion,
            IntPtr dwCallbackInstance,
            LINECALLPRIVILEGE dwPrivileges,
            LINEMEDIAMODE dwMediaModes,
            IntPtr lpCallParams);

        [DllImport("coredll")]
        extern static public int lineClose(IntPtr hLine);

        [DllImport("coredll")]
        extern static public int lineGetCallInfo(IntPtr hCall, byte[] lpCallInfo);

        [DllImport("coredll")]
        extern static public int lineDeallocateCall(IntPtr hCall);

        [DllImport("coredll")]
        extern static public int lineGetMessage(IntPtr m_hLineApp, out LINEMESSAGE lpMessage, int dwTimeout);

        [DllImport("coredll")]
        extern static public int lineShutdown(IntPtr m_hLineApp);

        [DllImport("coredll")]
        extern static public int lineNegotiateAPIVersion(
            IntPtr m_hLineApp,
            int dwDeviceID,
            int dwAPILowVersion,
            int dwAPIHighVersion,
            out int lpdwAPIVersion,
            out LINEEXTENSIONID lpExtensionID
            );

        [DllImport("coredll")]
        extern static public int lineGetDevCaps(IntPtr m_hLineApp,
            int dwDeviceID,
            int dwAPIVersion,
            int dwExtVersion,
            byte[] lpLineDevCaps
            );

        [DllImport("coredll")]
        extern static public int lineMonitorDigits(IntPtr hCall, LINEDIGITMODE dwDigitModes);

        [DllImport("coredll")]
        extern static public int lineGetDevConfig(
            int dwDeviceID,
            byte[] lpDeviceConfig,
            string lpszDeviceClass
            );

        [DllImport("coredll")]
        extern static public int lineMakeCall(
            IntPtr hLine,
            out IntPtr lphCall,
            string lpszDestAddress,
            int dwCountryCode,
            byte[] lpCallParams
            );

        [DllImport("coredll")]
        extern static public int lineHold(IntPtr hCall);

        [DllImport("coredll")]
        extern static public int lineGetCallStatus(IntPtr hCall, /*LPLINECALLSTATUS*/ byte[] lpCallStatus);

        [DllImport("coredll")]
        extern static public int lineDrop(
            IntPtr hCall,
            string lpsUserUserInfo,
            int dwSize
            );

        [DllImport("coredll")]
        extern static public int lineGetID(
            IntPtr hLine,
            int dwAddressID,
            IntPtr hCall,
            LINECALLSELECT dwSelect,
            /*LPVARSTRING*/
            byte[] lpDeviceID,
            string lpszDeviceClass
            );

        [DllImport("coredll")]
        extern static public int lineGetLineDevStatus(
            IntPtr hLine,
            /*LPLINEDEVSTATUS*/
            byte[] lpLineDevStatus
            );

        [DllImport("coredll")]
        extern static public int lineGetNewCalls(
            IntPtr hLine,
            int dwAddressID,
            LINECALLSELECT dwSelect,
            /*LPLINECALLLIST*/
            byte[] lpCallList
            );

        [DllImport("coredll")]
        extern static public int lineGetAddressID(
            IntPtr hLine,
            out int lpdwAddressID,
            LINEADDRESSMODE dwAddressMode,
            string lpsAddress,
            int dwSize
            );

        [DllImport("coredll")]
        extern static public int lineGetAddressCaps(
            IntPtr hLineApp,
            int dwDeviceID,
            int dwAddressID,
            int dwAPIVersion,
            int dwExtVersion,
            /*LPLINEADDRESSCAPS*/
            byte[] lpAddressCaps
            );

        [DllImport("coredll")]
        extern static public int lineGetAddressStatus(
            IntPtr hLine,
            int dwAddressID,
            /*LPLINEADDRESSSTATUS*/
            byte[] lpAddressStatus
            );

        [DllImport("coredll")]
        extern static public int lineSetStatusMessages(
            IntPtr hLine,
            LINEDEVSTATE dwLineStates,
            LINEADDRESSSTATE dwAddressStates
            );


        [DllImport("cellcore")]
        extern static public int lineSetEquipmentState(
                        IntPtr hLine,
                        LINEEQUIPSTATE dwState
                        );

        [DllImport("cellcore")]
        extern static public int lineGetEquipmentState(
                        IntPtr hLine,
                        out LINEEQUIPSTATE lpdwState,
                        out LINERADIOSUPPORT lpdwRadioSupport
                        );



        [DllImport("coredll")]
        extern static public int lineSetGPRSClass(
                        IntPtr hLine,
                        LINEGPRSCLASS dwClass
                        );


    }


    public class TapiException : Exception
    {
        public int NativeError;
        string message;
        public TapiException(int err)
        {
            NativeError = err;
        }
        public TapiException(string message, int err)
        {
            NativeError = err;
            this.message = message;
        }
        public override string Message
        {
            get
            {
                return string.Format("{0} {1}", message, ((LINEERR)NativeError));
            }
        }

    }

    #region TAPI Structures
    public class LINEINITIALIZEEXPARAMS
    {
        public LINEINITIALIZEEXPARAMS(IntPtr hEvent)
        {
            this.hEvent = hEvent;
            dwTotalSize = Marshal.SizeOf(typeof(LINEINITIALIZEEXPARAMS));
            dwOptions = LINEINITIALIZEEXOPTION_USEEVENT;
        }
        public int dwTotalSize;
        public int dwNeededSize;
        public int dwUsedSize;
        public int dwOptions;
        public IntPtr hEvent;
        public int dwCompletionKey;

        const int LINEINITIALIZEEXOPTION_USEEVENT = 0x2;
    }

    public struct LINEMESSAGE
    {
        public IntPtr hDevice;
        public LINEMESSAGES dwMessageID;
        public IntPtr dwCallbackInstance;
        public IntPtr dwParam1;
        public IntPtr dwParam2;
        public IntPtr dwParam3;

        public override string ToString()
        {
            switch (dwMessageID)
            {
                case LINEMESSAGES.LINE_CALLINFO:
                    return string.Format("{0}:{1}", dwMessageID, (LINECALLINFOSTATE)dwParam1.ToInt32());

                case LINEMESSAGES.LINE_CALLSTATE:
                    switch ((LINECALLSTATE)dwParam1.ToInt32())
                    {
                        case LINECALLSTATE.DISCONNECTED:
                            return string.Format("{0}:{1}:{2}", dwMessageID, (LINECALLSTATE)dwParam1.ToInt32(), (LINEDISCONNECTMODE)dwParam2.ToInt32());
                        default:
                            return string.Format("{0}:{1}", dwMessageID, (LINECALLSTATE)dwParam1.ToInt32());
                    }
                case LINEMESSAGES.LINE_REPLY:
                    return string.Format("{0}:{1}", dwMessageID, dwParam1);

                case LINEMESSAGES.LINE_DEVSPECIFIC:
                    switch ((LINEDEVSPECIFIC_CELLTSP)dwParam1.ToInt32())
                    {
                        case LINEDEVSPECIFIC_CELLTSP.LINE_REGISTERSTATE:
                            return string.Format("devspec:{0}:{1}", (LINEDEVSPECIFIC_CELLTSP)dwParam1.ToInt32(), (LINEREGSTATUS)dwParam2.ToInt32());
                        case LINEDEVSPECIFIC_CELLTSP.LINE_EQUIPSTATECHANGE:
                            return string.Format("devspec:{0}:{1}", (LINEDEVSPECIFIC_CELLTSP)dwParam1.ToInt32(), (LINEEQUIPSTATE)dwParam2.ToInt32());
                        default:
                            return string.Format("devspec:{0}", (LINEDEVSPECIFIC_CELLTSP)dwParam1.ToInt32());
                    }

                default:
                    return dwMessageID.ToString();
            }
        }

    }

    public struct LINECALLPARAMSDEVSPECIFIC
    {
        public CALLER_ID_OPTIONS cidoOptions;
    }
    public struct LINEEXTENSIONID
    {
        public IntPtr dwExtensionID0;
        public IntPtr dwExtensionID1;
        public IntPtr dwExtensionID2;
        public IntPtr dwExtensionID3;
    }

    public class LINEDEVCAPS : TapiStruct
    {
        public LINEDEVCAPS(int nSize)
            : base(nSize)
        {
            dwTotalSize = nSize;
        }
        public string LineName { get { return dwLineNameSize == 0 ? "" : Encoding.Unicode.GetString(Data, dwLineNameOffset, dwLineNameSize - 1); } }
        public string ProviderName
        {
            get
            {
                return dwProviderInfoSize == 0 ? "" : Encoding.Unicode.GetString(Data, dwProviderInfoOffset, dwProviderInfoSize - 1);
            }
        }
        public string[] DeviceClasses
        {
            get
            {
                string sClass = Encoding.Unicode.GetString(Data, dwDeviceClassesOffset, dwDeviceClassesSize - 1);

                return sClass.Split('\0');
            }
        }
        public int dwTotalSize;
        public int dwNeededSize;
        public int dwUsedSize;

        public int dwProviderInfoSize;
        public int dwProviderInfoOffset;

        public int dwSwitchInfoSize;
        public int dwSwitchInfoOffset;

        public int dwPermanentLineID;
        public int dwLineNameSize;
        public int dwLineNameOffset;
        public int dwStringFormat;
        public LINEADDRESSMODE dwAddressModes;
        public int dwNumAddresses;
        public LINEBEARERMODE dwBearerModes;
        public int dwMaxRate;
        public LINEMEDIAMODE dwMediaModes;

        public int dwGenerateToneModes;
        public int dwGenerateToneMaxNumFreq;
        public int dwGenerateDigitModes;
        public int dwMonitorToneMaxNumFreq;
        public int dwMonitorToneMaxNumEntries;
        public int dwMonitorDigitModes;
        public int dwGatherDigitsMinTimeout;
        public int dwGatherDigitsMaxTimeout;

        public int dwMedCtlDigitMaxListSize;
        public int dwMedCtlMediaMaxListSize;
        public int dwMedCtlToneMaxListSize;
        public int dwMedCtlCallStateMaxListSize;

        public LINEDEVCAPFLAGS dwDevCapFlags;
        public int dwMaxNumActiveCalls;
        public LINEANSWERMODE dwAnswerMode;
        public int dwRingModes;
        public LINEDEVSTATE dwLineStates;

        public int dwUUIAcceptSize;
        public int dwUUIAnswerSize;
        public int dwUUIMakeCallSize;
        public int dwUUIDropSize;
        public int dwUUISendUserUserInfoSize;
        public int dwUUICallInfoSize;

        public LINEDIALPARAMS MinDialParams;
        public LINEDIALPARAMS MaxDialParams;
        public LINEDIALPARAMS DefaultDialParams;

        public int dwNumTerminals;
        public int dwTerminalCapsSize;
        public int dwTerminalCapsOffset;
        public int dwTerminalTextEntrySize;
        public int dwTerminalTextSize;
        public int dwTerminalTextOffset;

        public int dwDevSpecificSize;
        public int dwDevSpecificOffset;

        public int dwLineFeatures;

        public int dwSettableDevStatus;
        public int dwDeviceClassesSize;
        public int dwDeviceClassesOffset;
    }

    public struct LINEDIALPARAMS
    {
        public int dwDialPause;
        public int dwDialSpeed;
        public int dwDigitDuration;
        public int dwWaitForDialtone;
    }

    public class LINECALLPARAMS : TapiStruct            // Defaults:
    {
        public LINECALLPARAMS(int size)
            : base(size)
        {
            dwTotalSize = size;
        }
        public int dwTotalSize;                    // ---------
        public LINEBEARERMODE dwBearerMode;                   // voice
        public int dwMinRate;                      // (3.1kHz)
        public int dwMaxRate;                      // (3.1kHz)
        public LINEMEDIAMODE dwMediaMode;                    // interactiveVoice
        public LINECALLPARAMFLAGS dwCallParamFlags;               // 0
        public LINEADDRESSMODE dwAddressMode;                  // addressID
        public int dwAddressID;                    // (any available)
        public LINEDIALPARAMS DialParams;                 // (0, 0, 0, 0)
        public int dwOrigAddressSize;              // 0
        public int dwOrigAddressOffset;
        public int dwDisplayableAddressSize;
        public int dwDisplayableAddressOffset;
        public int dwCalledPartySize;              // 0
        public int dwCalledPartyOffset;
        public int dwCommentSize;                  // 0
        public int dwCommentOffset;
        public int dwUserUserInfoSize;             // 0
        public int dwUserUserInfoOffset;
        public int dwHighLevelCompSize;            // 0
        public int dwHighLevelCompOffset;
        public int dwLowLevelCompSize;             // 0
        public int dwLowLevelCompOffset;
        public int dwDevSpecificSize;              // 0
        public int dwDevSpecificOffset;
        public int dwPredictiveAutoTransferStates;                 // TAPI v2.0
        public int dwTargetAddressSize;                            // TAPI v2.0
        public int dwTargetAddressOffset;                          // TAPI v2.0
        public int dwSendingFlowspecSize;                          // TAPI v2.0
        public int dwSendingFlowspecOffset;                        // TAPI v2.0
        public int dwReceivingFlowspecSize;                        // TAPI v2.0
        public int dwReceivingFlowspecOffset;                      // TAPI v2.0
        public int dwDeviceClassSize;                              // TAPI v2.0
        public int dwDeviceClassOffset;                            // TAPI v2.0
        public int dwDeviceConfigSize;                             // TAPI v2.0
        public int dwDeviceConfigOffset;                           // TAPI v2.0
        public int dwCallDataSize;                                 // TAPI v2.0
        public int dwCallDataOffset;                               // TAPI v2.0
        public int dwNoAnswerTimeout;                              // TAPI v2.0
        public int dwCallingPartyIDSize;                           // TAPI v2.0
        public int dwCallingPartyIDOffset;                         // TAPI v2.0
        public int dwAddressType;                                  // TAPI v3.0
    }

    public class LINECALLINFO : TapiStruct
    {
        public LINECALLINFO(int nSize)
            : base(nSize)
        {
            dwTotalSize = nSize;
        }
        public int dwTotalSize;
        public int dwNeededSize;
        public int dwUsedSize;
        public IntPtr hLine;
        public int dwLineDeviceID;
        public int dwAddressID;
        public LINEBEARERMODE dwBearerMode;
        public int dwRate;
        public LINEMEDIAMODE dwMediaMode;
        public int dwAppSpecific;
        public int dwCallID;
        public int dwRelatedCallID;
        public LINECALLPARAMFLAGS dwCallParamFlags;
        public LINECALLSTATE dwCallStates;
        public LINEDIGITMODE dwMonitorDigitModes;
        public LINEMEDIAMODE dwMonitorMediaModes;
        public LINEDIALPARAMS DialParams;
        public LINECALLORIGIN dwOrigin;
        public LINECALLREASON dwReason;
        public int dwCompletionID;
        public int dwNumOwners;
        public int dwNumMonitors;
        public int dwCountryCode;
        public int dwTrunk;
        public int dwCallerIDFlags;
        public int dwCallerIDSize;
        public int dwCallerIDOffset;
        public int dwCallerIDNameSize;
        public int dwCallerIDNameOffset;
        public int dwCalledIDFlags;
        public int dwCalledIDSize;
        public int dwCalledIDOffset;
        public int dwCalledIDNameSize;
        public int dwCalledIDNameOffset;
        public int dwConnectedIDFlags;
        public int dwConnectedIDSize;
        public int dwConnectedIDOffset;
        public int dwConnectedIDNameSize;
        public int dwConnectedIDNameOffset;
        public int dwRedirectionIDFlags;
        public int dwRedirectionIDSize;
        public int dwRedirectionIDOffset;
        public int dwRedirectionIDNameSize;
        public int dwRedirectionIDNameOffset;
        public int dwRedirectingIDFlags;
        public int dwRedirectingIDSize;
        public int dwRedirectingIDOffset;
        public int dwRedirectingIDNameSize;
        public int dwRedirectingIDNameOffset;
        public int dwAppNameSize;
        public int dwAppNameOffset;
        public int dwDisplayableAddressSize;
        public int dwDisplayableAddressOffset;
        public int dwCalledPartySize;
        public int dwCalledPartyOffset;
        public int dwCommentSize;
        public int dwCommentOffset;
        public int dwDisplaySize;
        public int dwDisplayOffset;
        public int dwUserUserInfoSize;
        public int dwUserUserInfoOffset;
        public int dwHighLevelCompSize;
        public int dwHighLevelCompOffset;
        public int dwLowLevelCompSize;
        public int dwLowLevelCompOffset;
        public int dwChargingInfoSize;
        public int dwChargingInfoOffset;
        public int dwTerminalModesSize;
        public int dwTerminalModesOffset;
        public int dwDevSpecificSize;
        public int dwDevSpecificOffset;
        public int dwCallTreatment;                                // TAPI v2.0
        public int dwCallDataSize;                                 // TAPI v2.0
        public int dwCallDataOffset;                               // TAPI v2.0
        public int dwSendingFlowspecSize;                          // TAPI v2.0
        public int dwSendingFlowspecOffset;                        // TAPI v2.0
        public int dwReceivingFlowspecSize;                        // TAPI v2.0
        public int dwReceivingFlowspecOffset;                      // TAPI v2.0
        public int dwAddressType;                                  // TAPI v3.0
    }

    /// <summary>
    /// This structure describes the current status of a line device
    /// </summary>
    public class LINEDEVSTATUS : TapiStruct
    {
        public LINEDEVSTATUS(int nSize)
            : base(nSize)
        {
            dwTotalSize = nSize;
        }
        public int dwTotalSize;
        public int dwNeededSize;
        public int dwUsedSize;

        public int dwNumOpens;
        public int dwOpenMediaModes;
        public int dwNumActiveCalls;
        public int dwNumOnHoldCalls;
        public int dwNumOnHoldPendCalls;
        /// <summary>
        /// Specifies the line-related API functions that are currently available on this line. 
        /// </summary>
        public LINEFEATURE dwLineFeatures;
        public int dwNumCallCompletions;
        public int dwRingMode;
        public int dwSignalLevel;
        public int dwBatteryLevel;
        public LINEROAMMODE dwRoamMode;

        public int dwDevStatusFlags;

        public int dwTerminalModesSize;
        public int dwTerminalModesOffset;

        public int dwDevSpecificSize;
        public int dwDevSpecificOffset;
    }

    public class LINECALLLIST : TapiStruct
    {
        public LINECALLLIST(int size)
            : base(size)
        {
            dwTotalSize = size;
        }
        public int dwTotalSize;
        public int dwNeededSize;
        public int dwUsedSize;
        public int dwCallsNumEntries;
        public int dwCallsSize;
        public int dwCallsOffset;
    }

    public class LINEADDRESSCAPS : TapiStruct
    {
        public LINEADDRESSCAPS(int size)
            : base(size)
        {
            dwTotalSize = size;
        }
        public int dwTotalSize;
        public int dwNeededSize;
        public int dwUsedSize;
        public int dwLineDeviceID;
        public int dwAddressSize;
        public int dwAddressOffset;
        public int dwDevSpecificSize;
        public int dwDevSpecificOffset;
        public int dwAddressSharing;
        public int dwAddressStates;
        public LINECALLINFOSTATE dwCallInfoStates;
        public int dwCallerIDFlags;
        public int dwCalledIDFlags;
        public int dwConnectedIDFlags;
        public int dwRedirectionIDFlags;
        public int dwRedirectingIDFlags;
        public LINECALLSTATE dwCallStates;
        public int dwDialToneModes;
        public int dwBusyModes;
        public int dwSpecialInfo;
        public LINEDISCONNECTMODE dwDisconnectModes;
        public int dwMaxNumActiveCalls;
        public int dwMaxNumOnHoldCalls;
        public int dwMaxNumOnHoldPendingCalls;
        public int dwMaxNumConference;
        public int dwMaxNumTransConf;
        public int dwAddrCapFlags;
        public int dwCallFeatures;
        public int dwRemoveFromConfCaps;
        public int dwRemoveFromConfState;
        public int dwTransferModes;
        public int dwParkModes;
        public LINEFORWARDMODE dwForwardModes;
        public int dwMaxForwardEntries;
        public int dwMaxSpecificEntries;
        public int dwMinFwdNumRings;
        public int dwMaxFwdNumRings;
        public int dwMaxCallCompletions;
        public int dwCallCompletionConds;
        public int dwCallCompletionModes;
        public int dwNumCompletionMessages;
        public int dwCompletionMsgTextEntrySize;
        public int dwCompletionMsgTextSize;
        public int dwCompletionMsgTextOffset;

        public int dwAddressFeatures;                              // TAPI v1.4

        public int dwPredictiveAutoTransferStates;                 // TAPI v2.0
        public int dwNumCallTreatments;                            // TAPI v2.0
        public int dwCallTreatmentListSize;                        // TAPI v2.0
        public int dwCallTreatmentListOffset;                      // TAPI v2.0
        public int dwDeviceClassesSize;                            // TAPI v2.0
        public int dwDeviceClassesOffset;                          // TAPI v2.0
        public int dwMaxCallDataSize;                              // TAPI v2.0
        public int dwCallFeatures2;                                // TAPI v2.0
        public int dwMaxNoAnswerTimeout;                           // TAPI v2.0
        public int dwConnectedModes;                               // TAPI v2.0
        public int dwOfferingModes;                                // TAPI v2.0
        public int dwAvailableMediaModes;                          // TAPI v2.0

    }

    public class LINEADDRESSSTATUS : TapiStruct
    {
        public LINEADDRESSSTATUS(int size)
            : base(size)
        {
            dwTotalSize = size;
        }
        public int dwTotalSize;
        public int dwNeededSize;
        public int dwUsedSize;
        public int dwNumInUse;
        public int dwNumActiveCalls;
        public int dwNumOnHoldCalls;
        public int dwNumOnHoldPendCalls;
        public int dwAddressFeatures;
        public int dwNumRingsNoAnswer;
        public int dwForwardNumEntries;
        public int dwForwardSize;
        public int dwForwardOffset;
        public int dwTerminalModesSize;
        public int dwTerminalModesOffset;
        public int dwDevSpecificSize;
        public int dwDevSpecificOffset;

    }

    public class LINECALLSTATUS : TapiStruct
    {
        public LINECALLSTATUS(int size)
            : base(size)
        {
            dwTotalSize = size;
        }
        public int dwTotalSize;
        public int dwNeededSize;
        public int dwUsedSize;
        public LINECALLSTATE dwCallState;
        public int dwCallStateMode;
        public LINECALLPRIVILEGE dwCallPrivilege;
        public LINECALLFEATURE dwCallFeatures;
        public int dwDevSpecificSize;
        public int dwDevSpecificOffset;
        public LINECALLFEATURE2 dwCallFeatures2;
        public int StateEntryTimeLow;
        public int StateEntryTimeHigh;
    }


    public class VARSTRING : TapiStruct
    {
        public VARSTRING(int size)
            : base(size)
        {
            dwTotalSize = size;
        }
        public int dwTotalSize;
        public int dwNeededSize;
        public int dwUsedSize;
        public int dwStringFormat;
        public int dwStringSize;
        public int dwStringOffset;
    }

    public class TapiStruct
    {
        [Internal]
        byte[] m_data;
        public TapiStruct(int nSize)
        {
            m_data = new byte[nSize];
            InitStructs(this);
        }
        public void Load()
        {
            ByteCopy.ByteArrayToStruct(m_data, this);
        }
        public void Store()
        {
            ByteCopy.StructToByteArray(this, m_data);
        }
        public byte[] Data { get { return m_data; } set { m_data = value; } }

        protected object InitStructs(object obj)
        {
            foreach (FieldInfo fi in obj.GetType().GetFields(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance))
            {
                Type t = fi.FieldType;

                if (t.IsArray)
                {
                    object[] colAttr = fi.GetCustomAttributes(typeof(ArrayAttribute), true);

                    if (colAttr.Length != 1)
                        throw new NotSupportedException(string.Format("Field {0}: Must have Array attribute with size specified", fi.Name));

                    int size = (colAttr[0] as ArrayAttribute).Size;

                    fi.SetValue(obj, Array.CreateInstance(fi.FieldType.GetElementType(), size));
                }
                else if (t.IsValueType && !t.IsPrimitive)
                {
                    fi.SetValue(obj, InitStructs(fi.GetValue(obj)));
                }
            }

            return obj;
        }

    }


    #endregion
}
