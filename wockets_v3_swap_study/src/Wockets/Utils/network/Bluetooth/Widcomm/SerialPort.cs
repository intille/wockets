//==========================================================================================
//
//		OpenNETCF.IO.Ports.SerialPort
//		Copyright (c) 2005, OpenNETCF.org
//
//		This library is free software; you can redistribute it and/or modify it under 
//		the terms of the OpenNETCF.org Shared Source License.
//
//		This library is distributed in the hope that it will be useful, but 
//		WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or 
//		FITNESS FOR A PARTICULAR PURPOSE. See the OpenNETCF.org Shared Source License 
//		for more details.
//
//		You should have received a copy of the OpenNETCF.org Shared Source License 
//		along with this library; if not, email licensing@opennetcf.org to request a copy.
//
//		If you wish to contact the OpenNETCF Advisory Board to discuss licensing, please 
//		email licensing@opennetcf.org.
//
//		For general enquiries, email enquiries@opennetcf.org or visit our website at:
//		http://www.opennetcf.org
//
//==========================================================================================

using System;
using System.Runtime.InteropServices;
using System.Threading;
using System.Collections;
using System.Text;
using System.ComponentModel;
using OpenNETCF.IO.Serial;

namespace OpenNETCF.IO.Ports {

	/// <summary>
	/// Represents a serial port resource.
	/// <para><b>New in v1.3</b></para>
	/// </summary>
#if DESIGN
	[ToolboxItemFilter("NETCF",ToolboxItemFilterType.Require),
	ToolboxItemFilter("System.CF.Windows.Forms", ToolboxItemFilterType.Custom)]
#endif
	public class SerialPort : Component, IDisposable 
	{

		#region Events
		public event SerialDataReceivedEventHandler DataReceived;
		public event SerialErrorReceivedEventHandler ErrorReceived;
		public event SerialPinChangedEventHandler PinChanged;
		#endregion

		
		#region Creation Destruction
		/// <summary>
		/// Not Currently Supported. Initializes a new instance of the <see cref="SerialPort"/> class using the <see cref="System.ComponentModel.IContainer"/> object specified.
		/// </summary>
		/// <param name="container">An interface to a container.</param>
		public SerialPort(IContainer container) : this() {
			// add designer support. Low priority as you can still create it in code
			//container.Add(this);
			throw new NotSupportedException("not yet");
		}
		/// <summary>
		/// Initializes a new instance of the <see cref="SerialPort"/> class.
		/// </summary>
		public SerialPort(){
			// create the API class based on the target
			if (System.Environment.OSVersion.Platform != PlatformID.WinCE)
				m_CommAPI = new WinCommAPI();
			else
				m_CommAPI = new CECommAPI();

			// create a system event for synchronizing Closing
			this.mCloseEvent = m_CommAPI.CreateEvent(true, false, CloseEventName);
		}

		/// <summary>
		/// Initializes a new instance of the <see cref="SerialPort"/> class using the specified port name.
		/// </summary>
		/// <param name="portName">A string indicating the port to be used, for example, COM1.</param>
		public SerialPort(string portName) : this(portName, 9600, Parity.None, 8, StopBits.One) {}

		/// <summary>
		/// Initializes a new instance of the <see cref="SerialPort"/> class using the specified port name, baud rate and parity bit.
		/// </summary>
		/// <param name="portName">A string indicating the port to be used, for example, COM1.</param>
		/// <param name="baudRate">An integer indicating the baud rate.</param>
		public SerialPort(string portName, int baudRate) : this(portName, baudRate, Parity.None, 8, StopBits.One) {}
		/// <summary>
		/// Initializes a new instance of the <see cref="SerialPort"/> class using the specified port name, baud rate and parity bit.
		/// </summary>
		/// <param name="portName">A string indicating the port to be used, for example, COM1.</param>
		/// <param name="baudRate">An integer indicating the baud rate.</param>
		/// <param name="parity">A value from the <see cref="Parity"/> enumeration.</param>
		public SerialPort(string portName, int baudRate, Parity parity) : this(portName, baudRate, parity, 8, StopBits.One) {}

		/// <summary>
		/// Initializes a new instance of the <see cref="SerialPort"/> class using the specified port name, baud rate, parity bit and data bits.
		/// </summary>
		/// <param name="portName">A string indicating the port to be used, for example, COM1.</param>
		/// <param name="baudRate">An integer indicating the baud rate.</param>
		/// <param name="parity">A value from the <see cref="Parity"/> enumeration.</param>
		/// <param name="dataBits">An integer indicating the data bits value.</param>
		public SerialPort(string portName, int baudRate, Parity parity, int dataBits) : this(portName, baudRate, parity, dataBits, StopBits.One) {}

		/// <summary>
		/// Initializes a new instance of the <see cref="SerialPort"/> class using the specified port name, baud rate, parity bit, data bits and stop bit.
		/// </summary>
		/// <param name="portName">A string indicating the port to be used, for example, COM1.</param>
		/// <param name="baudRate">An integer indicating the baud rate.</param>
		/// <param name="parity">A value from the <see cref="Parity"/> enumeration.</param>
		/// <param name="dataBits">An integer indicating the data bits value.</param>
		/// <param name="stopBits">A value from the <see cref="StopBits"/> enumeration.</param>
		public SerialPort(string portName, int baudRate, Parity parity, int dataBits, StopBits stopBits) : this() {
			this.PortName = portName;
			this.BaudRate = baudRate;
			this.Parity = parity;
			this.DataBits = dataBits;
			this.StopBits = stopBits;
		}

		/// <summary>
		/// Releases the unmanaged resources used by the <see cref="SerialPort"/> object.
		/// </summary>
		public void Dispose() {
			if(this.mIsOpen)
				this.Close();
			//base.Dispose(true);			
		}
		
		/// <summary>
		/// Class destructor
		/// </summary>
		~SerialPort() {
			if(this.mIsOpen)
				this.Close();
		}
		#endregion

		#region Private Fields
		private Encoding mEncoding = Encoding.ASCII;
		private Decoder mDecoder = Encoding.ASCII.GetDecoder();
		private string mNewLine = @"\n";
		private byte mByteSize = 8;
		private bool mDiscardNull = false;
		private Handshake mHandshake = Handshake.None;
		private byte mErrorChar = 0x3f; //?
		private StopBits mStopBits = StopBits.One;
		private int mWriteTimeout = InfiniteTimeout;
		private int mReadTimeout = InfiniteTimeout;
		private int mRxBufferSize = 4096;
		private int mTxBufferSize = 2048;
		private int	mRts = 0;
		private int mRthreshold = 1;
		private string mPortName = "COM1:";
		private Parity mParity = Parity.None;
		private bool mIsOpen = false;
		private int	mDtr = 1;
		private bool mInBreak = false;
		private int mBaudRate = 9600;
		private IntPtr hPort = (IntPtr)CommAPI.INVALID_HANDLE_VALUE;
		private DCB mDcb = new DCB();
		private Thread mEventThread = null;
		private ManualResetEvent mThreadStarted = new ManualResetEvent(false);
		private IntPtr mCloseEvent;
		private IntPtr mTxOverlapped = IntPtr.Zero;
		private IntPtr mRxOverlapped = IntPtr.Zero;
		private const string CloseEventName = "CloseEvent";
		private CommAPI m_CommAPI = null;
		private int mReadPos = 0;
		private int mReadLen = 0;
		private byte[] mInBuffer = new byte[1024];
		#endregion

		#region Public Properties
		/// <summary>
		/// Indicates that no timeout should occur.
		/// </summary>
#if DESIGN
		[Browsable(false)]
#endif
		public const int InfiniteTimeout = -1; 
		/// <summary>
		/// Gets the underlying System.IO.Stream object for a OpenNETCF.IO.Ports.SerialPort object.
		/// </summary>
		/// <returns>A System.IO.Stream object.</returns>
		public System.IO.Stream BaseStream() {
			// some day in the distant future someone else may want to consider providing this
			throw new NotSupportedException("BaseStream Not supported");
		}
		/// <summary>
		/// Gets or sets the value used to interpret the end of a call to the <see cref="ReadLine"/> and <see cref="WriteLine"/> methods.
		/// </summary>
#if DESIGN
		[Browsable(false)]
#endif
		public string NewLine {
			get {
				return this.mNewLine;
			}
			set {
				if (value == null) {
					throw new ArgumentNullException();
				}
				if (value.Length == 0) {
					throw new ArgumentException("NewLine cannot be empty");
				}
				this.mNewLine = value;
			}
		}

		/// <summary>
		/// Gets or sets the serial baud rate.
		/// </summary>
		/// <returns>An integer object representing the baud rate.</returns>
#if DESIGN
	[DefaultValue(9600)]
#endif
		public int BaudRate 
		{
			get {
				return this.mBaudRate;
			}
			set {
				if (value <= 0) {
					throw new ArgumentOutOfRangeException("BaudRate must be > 0");
				}
				this.mBaudRate = value;
				if (this.IsOpen) {
					this.UpdateSettings();
				}
			}
		}
		/// <summary>
		/// Gets or sets the break signal state.
		/// </summary>
		/// <returns>true to enter a break state; otherwise false.</returns>
#if DESIGN
	[Browsable(false)]
#endif
		public bool BreakState 
		{
			get {
				if (!this.IsOpen) {
					throw new InvalidOperationException("Port is not open");
				}
				return this.mInBreak;
			}
			set {
				if (!this.IsOpen) {
					throw new InvalidOperationException("Port is not open");
				}
				if (value) {
					if (!m_CommAPI.EscapeCommFunction(hPort, CommEscapes.SETBREAK)) {
						throw new ApplicationException("Failed to set break");
					}
					this.mInBreak = true;
				}
				else {
					if (!m_CommAPI.EscapeCommFunction(hPort, CommEscapes.CLRBREAK)) {
						throw new ApplicationException("Failed to clear break");
					}
					this.mInBreak = false;
				}
			}
		}
		/// <summary>
		/// Gets the number of bytes of data in the receive buffer.
		/// </summary>
		/// <return>The number of bytes of data in the receive buffer.</return>
#if DESIGN
	[Browsable(false)]
#endif
		public int BytesToRead 
		{
			get {
				if (!this.IsOpen) {
					throw new InvalidOperationException("Port is not open");
				}
				CommErrorFlags errorFlags = new CommErrorFlags();
				CommStat commStat = new CommStat();				
				if(!m_CommAPI.ClearCommError(hPort, ref errorFlags, commStat)) {
					throw new ApplicationException("Failed to clear error/read");
				}
				return (int)commStat.cbInQue + (this.mReadLen - this.mReadPos);
			}
		}

		/// <summary>
		/// Gets the number of bytes of data in the send buffer.
		/// </summary>
		/// <return>The number of bytes of data in the send buffer.</return>
#if DESIGN
	[Browsable(false)]
#endif
		public int BytesToWrite {
			get {
				if (!this.IsOpen) {
					throw new InvalidOperationException("Port is not open");
				}
				CommErrorFlags errorFlags = new CommErrorFlags();
				CommStat commStat = new CommStat();				
				if(!m_CommAPI.ClearCommError(hPort, ref errorFlags, commStat)) {
					throw new ApplicationException("Failed to clear error/write");
				}
				return (int)commStat.cbOutQue;
			}
		}

		/// <summary>
		/// Gets the state of the Carrier Detect line for the port.
		/// </summary>
		/// <return>true if carrier is detected; otherwise false.</return>
#if DESIGN
	[Browsable(false)]
#endif
		public bool CDHolding 
		{
			get {
				if (!this.IsOpen) {
					throw new InvalidOperationException("Port is not open");
				}
				uint status = 0;
				if (!m_CommAPI.GetCommModemStatus(hPort, ref status)) {
					throw new ApplicationException("Failed to get CD");
				}
				return ((((uint)CommModemStatusFlags.MS_RLSD_ON) & status) != 0);
			}
		}

		/// <summary>
		/// Gets the state of the Clear-to-Send line.
		/// </summary>
		/// <return>true if Clear-to-Send detected; otherwise false.</return>
#if DESIGN
	[Browsable(false)]
#endif
		public bool CtsHolding 
		{
			get {
				if (!this.IsOpen) {
					throw new InvalidOperationException("Port is not open");
				}
				uint status = 0;
				if (!m_CommAPI.GetCommModemStatus(hPort, ref status)) {
					throw new ApplicationException("Failed to get CTS");
				}
				return ((((uint)CommModemStatusFlags.MS_CTS_ON) & status) != 0);
			}
		}


		/// <summary>
		/// Gets or sets the standard length of data bits per byte.
		/// </summary>
		/// <return>An integer object specifying the data bits length.</return>
#if DESIGN
	[DefaultValue(8)]
#endif
		public int DataBits 
		{
			get {
				return this.mByteSize;
			}
			set {
				if ((value < 5) || (value > 8)) {
					throw new ArgumentOutOfRangeException("DataBits must be >=5 <=8");
				}
				this.mByteSize = (byte)value;
				if (this.IsOpen) {
					this.UpdateSettings();
				}
			}
		}
		/// <summary>
		/// Gets or sets whether null bytes are ignored when transmitted between the port and the receive buffer.
		/// </summary>
		/// <return>true if null bytes are ignored; otherwise false. The default value for this property is false.</return>
#if DESIGN
	[DefaultValue(false)]
#endif
		public bool DiscardNull 
		{
			get {
				return this.mDiscardNull;
			}
			set {
				this.mDiscardNull = value;
				if (this.IsOpen) {
					this.UpdateSettings();
				}
			}
		}

		/// <summary>
		/// Gets the state of the Data Set Ready (DSR) signal.
		/// </summary>
		/// <return>true if a Data Set Ready signal has been sent to the port; otherwise false.</return>
#if DESIGN
	[Browsable(false)]
#endif
		public bool DsrHolding 
		{
			get {
				if (!this.IsOpen) {
					throw new InvalidOperationException("Port is not open");
				}
				uint status = 0;
				if (!m_CommAPI.GetCommModemStatus(hPort, ref status)) {
					throw new ApplicationException("Failed to get DSR");
				}
				return ((((uint)CommModemStatusFlags.MS_DSR_ON) & status) != 0);
			}
		}

		/// <summary>
		/// Gets or sets enabling of the Data Terminal Ready (DTR) signal during serial communication.
		/// </summary>
		/// <return>true to enable DTR, otherwise false.</return>
#if DESIGN
	[DefaultValue(false)]
#endif
		public bool DtrEnable {
			get 
			{
				return (this.mDtr == 1);
			}
			set {
				if (value){
					this.mDtr = 1;
				}else{
					this.mDtr = 0;
				}
				if (this.IsOpen){
					this.UpdateSettings();

					if (!m_CommAPI.EscapeCommFunction(hPort, ((this.mDtr == 1) ? CommEscapes.SETDTR : CommEscapes.CLRDTR))){
						throw new ApplicationException("Failed to set/clear DTR!");
					}
				}
			}
		}
		
		/// <summary>
		/// Gets or sets the handshaking protocol for serial port transmission of data.
		/// </summary>
		/// <return>A value of the enumeration <see cref="Handshake"/>.</return>
#if DESIGN
	[DefaultValue(0x0)]
#endif
		public Handshake Handshake 
		{
			get {
				return this.mHandshake;
			}
			set {
				if ((value < Handshake.None) || (value > Handshake.RequestToSendXOnXOff)) {
					throw new ArgumentOutOfRangeException("Handshake. Use the enum");
				}
				this.mHandshake = value;
				if (this.IsOpen) {
					this.UpdateSettings();
				}
			}
		}

		/// <summary>
		/// Gets the open or closed status of the <see cref="SerialPort"/> object.
		/// </summary>
		/// <return>true if the serial port is open, otherwise false.</return>
#if DESIGN
	[Browsable(false)]
#endif
		public bool IsOpen 
		{
			get {
				return this.mIsOpen;
			}
		}
		/// <summary>
		/// Gets or sets the parity-checking protocol.
		/// </summary>
		/// <return>A <see cref="Parity"/> object that represents the parity-checking protocol.</return>
#if DESIGN
	[DefaultValue(0x0)]
#endif
		public Parity Parity {
			get 
			{
				return this.mParity;
			}
			set {
				if ((value < Parity.None) || (value > Parity.Space)) {
					throw new ArgumentOutOfRangeException("Parity. Use the enum");
				}
				this.mParity = value;
				if (this.IsOpen) {
					this.UpdateSettings();
				}
			}
		}
		/// <summary>
		/// Gets or sets the byte that is used to replace invalid characters in a data stream when a parity error occurs.
		/// </summary>
		/// <return>A byte used to replace invalid characters.</return>
#if DESIGN
	[DefaultValue(63)]
#endif
		public byte ParityReplace {
			get 
			{
				return this.mErrorChar;
			}
			set {
				this.mErrorChar = value;
				if (this.IsOpen) {
					this.UpdateSettings();
				}
			}
		}
		/// <summary>
		/// Gets or sets the port for communications, including but not limited to all available COM ports.
		/// </summary>
		/// <value>A string object representing the communications port e.g. "COM1", "COM10" etc.</value>
#if DESIGN
	[DefaultValue("COM1")]
#endif		
		public string PortName {
			get 
			{
				//trim the last colon if present
				return this.mPortName.Trim(new char[]{'\\','.',':'});
				//return this.mPortName.TrimEnd(new char[]{':'});
				
			}
			set {
				if(! CommAPI.FullFramework) {
					if(! value.EndsWith(":")) {
						//append the colon
						this.mPortName = "\\\\.\\" + value + ":";
						return;
						//throw new ApplicationException("On WinCE comm port must end with :");						
					}
				}

				this.mPortName = value;
			}
		}

		/// <summary>
		/// Gets or sets the number of bytes in the internal input buffer before a OpenNETCF.IO.Ports.SerialPort.ReceivedEvent is fired.
		/// </summary>
		/// <return>An integer object.</return>
#if DESIGN
	[DefaultValue(1)]
#endif
		public int ReceivedBytesThreshold 
		{
			get {
				return this.mRthreshold;
			}
			set {
				this.mRthreshold = value;
			}
		}

		/// <summary>
		/// Gets or sets the standard number of stopbits per byte.
		/// </summary>
		/// <return>A value of the enumeration <see cref="StopBits"/>.</return>
#if DESIGN
	[DefaultValue(1)]
#endif		
		public StopBits StopBits {
			get 
			{
				return this.mStopBits;
			}
			set {
				if ((value < StopBits.One) || (value > StopBits.OnePointFive)) {
					throw new ArgumentOutOfRangeException("StopBits. Use the Enum");
				}
				this.mStopBits = value;
				if (this.IsOpen) {
					this.UpdateSettings();
				}
			}
		}
		/// <summary>
		/// Gets or sets whether the Request to Transmit (RTS) signal is enabled during serial communication.
		/// </summary>
		/// <return>true to enable RTS, otherwise false.</return>
#if DESIGN
	[DefaultValue(false)]
#endif
		public bool RtsEnable {
			get 
			{
				return (this.mRts == 1);
			}
			set {
				if(this.mRts < 0) return;
				if(hPort == (IntPtr)CommAPI.INVALID_HANDLE_VALUE) return;

				if (value) {
					if (m_CommAPI.EscapeCommFunction(hPort, CommEscapes.SETRTS))
						this.mRts = 1;
					else
						throw new ApplicationException("Failed to set RTS!");
				}
				else {
					if (m_CommAPI.EscapeCommFunction(hPort, CommEscapes.CLRRTS))
						this.mRts = 0;
					else
						throw new ApplicationException("Failed to clear RTS!");
				}
			}
		}
		
		/// <summary>
		/// Gets or sets the number of milliseconds before a timeout occurs when a write operation does not finish.
		/// </summary>
		/// <return>An integer object.</return>
#if DESIGN
	[DefaultValue(-1)]
#endif
		public int WriteTimeout {
			get 
			{
				return this.mWriteTimeout;
			}
			set {
				if ((value == 0) || (value < InfiniteTimeout)) {
					throw new ArgumentOutOfRangeException("WriteTimeout. Only valid negative value is -1");
				}
				this.mWriteTimeout = value;
				if (this.IsOpen) {
					this.UpdateTimeouts();
				}
			}
		}
		/// <summary>
		/// Gets or sets the number of milliseconds before a timeout occurs when a read operation does not finish.
		/// </summary>
		/// <return>An integer object.</return>
#if DESIGN
	[DefaultValue(-1)]
#endif
		public int ReadTimeout {
			get 
			{
				return this.mReadTimeout;
			}
			set {
				if (value < InfiniteTimeout) {
					throw new ArgumentOutOfRangeException("ReadTimeout. Cannot be 0 or <-1");
				}
				this.mReadTimeout = value;
				if (this.IsOpen) {
					this.UpdateTimeouts();
				}
			}
		}
		/// <summary>
		/// Gets or sets the size of the serial port output buffer.
		/// </summary>
		/// <return>An integer value representing the size of the output buffer. The default value is 2048.</return>
#if DESIGN
	[DefaultValue(2048)]
#endif
		public int WriteBufferSize {
			get 
			{
				return this.mTxBufferSize;
			}
			set {
				if (value <= 0) {
					throw new ArgumentOutOfRangeException("WriteBufferSize must be > 0");
				}
				this.mTxBufferSize = value;
				if (this.IsOpen) {					
					throw new InvalidOperationException("WriteBufferSize cannot be set when open");
				}
			}
		}
		/// <summary>
		/// Gets or sets the size of the <see cref="SerialPort"/> input buffer.
		/// </summary>
		/// <return>An integer value representing the buffer size The default value is 4096..</return>
#if DESIGN
	[DefaultValue(4096)]
#endif
		public int ReadBufferSize {
			get 
			{
				return this.mRxBufferSize;
			}
			set {
				if (value <= 0) {
					throw new ArgumentOutOfRangeException("ReadBufferSize must be > 0");
				}
				this.mRxBufferSize = value;
				if (this.IsOpen) {
					throw new InvalidOperationException("ReadBufferSize cannot be set when open");
				}
			}
		} 
		/// <summary>
		/// Gets or sets the character encoding for pre- and post-transmission conversion of text.
		/// </summary>
		/// <return>A <see cref="System.Text.Encoding"/> object.</return>
#if DESIGN
	[Browsable(false)]
#endif
		public Encoding Encoding 
		{
			get {
				return this.mEncoding;
			}
			set {
				if (value == null) {
					throw new ArgumentNullException("Encoding");
				}
				this.mEncoding = value;
				this.mDecoder = this.mEncoding.GetDecoder();
			}
		}

		#endregion

		#region Public Methods
		/// <summary>
		/// Not Currently Supported. Gets an array of serial port names for the current machine.
		/// </summary>
		/// <returns>An array of serial port names for the current machine.</returns>
		public static string[] GetPortNames() {
			// TODO iterate over reg key and return array of port names
			// @"HARDWARE\DEVICEMAP\SERIALCOMM"
			throw new NotSupportedException("not yet");
		}

		/// <summary>
		/// Discards data from the serial driver's receive buffer.
		/// </summary>
		public void DiscardInBuffer() {
			if (!this.IsOpen) {
				throw new InvalidOperationException("Port is not open");
			}

			if (m_CommAPI.PurgeComm(hPort, 10) != 0 ) {
				throw new ApplicationException("could not discard in buffer");
			}

			this.mReadLen = 0;
			this.mReadPos = 0;
		}
		/// <summary>
		/// Discards data from the serial driver's transmit buffer.
		/// </summary>
		public void DiscardOutBuffer() {
			if (!this.IsOpen) {
				throw new InvalidOperationException("Port is not open");
			}

			if (m_CommAPI.PurgeComm(hPort, 5) != 0 ) {
				throw new ApplicationException("could not discard out buffer");
			}
		}

		/// <summary>
		/// Opens a new serial port connection.
		/// </summary>
		public void Open() {
			if(this.mIsOpen) throw new InvalidOperationException("Comm Port is already open!");

			if(CommAPI.FullFramework) {
				// set up the overlapped tx IO
				OVERLAPPED o = new OVERLAPPED();
				this.mTxOverlapped = LocalAlloc(0x40, Marshal.SizeOf(o));
				o.Offset = 0; 
				o.OffsetHigh = 0;
				o.hEvent = IntPtr.Zero;
				Marshal.StructureToPtr(o, this.mTxOverlapped, true);
			}

			hPort = m_CommAPI.CreateFile(this.mPortName);
          
			if(hPort == (IntPtr)CommAPI.INVALID_HANDLE_VALUE) {
				int e = Marshal.GetLastWin32Error();

				if(e == (int)APIErrors.ERROR_ACCESS_DENIED) {
					// port is unavailable
					throw new ApplicationException("ERROR_ACCESS_DENIED");
				}

				// ClearCommError failed!
				string error = String.Format("CreateFile Failed: {0}", e);
				throw new ApplicationException(error);
			}

			
			this.mIsOpen = true;

			// clear errors
			CommErrorFlags errorFlags = new CommErrorFlags();
			CommStat commStat = new CommStat();				
			if(!m_CommAPI.ClearCommError(hPort, ref errorFlags, commStat)) {
				throw new ApplicationException("Failed to clear error/read");
			}

			// set queue sizes
			m_CommAPI.SetupComm(hPort, this.mRxBufferSize, this.mTxBufferSize);

			// update dcb
			this.UpdateSettings();

			// store some state values
			this.mInBreak = false;

			// read/write timeouts
			this.UpdateTimeouts();

			// start the receive thread
			this.mEventThread = new Thread(new ThreadStart(CommEventThread));
			this.mEventThread.Priority = ThreadPriority.Normal; //by design
			this.mEventThread.Start();

			// wait for the thread to actually get spun up
			this.mThreadStarted.WaitOne();
		}

		/// <summary>
		/// Closes the port connection, sets OpenNETCF.IO.Ports.SerialPort.IsOpen to false and disposes of the internal System.IO.Stream object.
		/// </summary>
		public void Close() {
			if(this.mTxOverlapped != IntPtr.Zero) {
				LocalFree(this.mTxOverlapped);
				this.mTxOverlapped = IntPtr.Zero;
			}

			if(!this.mIsOpen) return;

			this.mIsOpen = false; // to help catch intentional close
            this.mEventThread.Abort();            
			if(m_CommAPI.CloseHandle(hPort)) {
				m_CommAPI.SetEvent(this.mCloseEvent);

				this.mIsOpen = false;

				hPort = (IntPtr)CommAPI.INVALID_HANDLE_VALUE;
				
				m_CommAPI.SetEvent(this.mCloseEvent);
			}


		}


		#region Read
		/// <summary>
		/// Reads a number of bytes from the OpenNETCF.IO.Ports.SerialPort input buffer and writes those bytes into a character array at a given offset.
		/// </summary>
		/// <param name="buffer">The byte array to which the input is written.</param>
		/// <param name="offset">The offset in the buffer array where writing should begin.</param>
		/// <param name="count">The number of bytes to be read.</param>
		public int Read(byte[] buffer, int offset, int count) {
			if (!this.IsOpen) {
				throw new InvalidOperationException("Port is not open");
			}
			if (buffer == null) {
				throw new ArgumentNullException("buffer");
			}
			if (offset < 0) {
				throw new ArgumentOutOfRangeException("offset must be > 0");
			}
			if (count < 0) {
				throw new ArgumentOutOfRangeException("count must be > 0");
			}
			if ((buffer.Length - offset) < count) {
				throw new ArgumentException("Failed: ((buffer.Length - offset) < count)");
			}
			int bytesToRead = 0;
			if ((this.mReadLen - this.mReadPos) >= 1) {
				bytesToRead = Math.Min((this.mReadLen - this.mReadPos), count);
				Buffer.BlockCopy(this.mInBuffer, this.mReadPos, buffer, offset, bytesToRead);
				this.mReadPos += bytesToRead;
				if (bytesToRead == count) {
					if (this.mReadPos == this.mReadLen) {
						this.mReadLen = 0;
						this.mReadPos = 0;
					}
					return count;
				}
				if (this.BytesToRead == 0) {
					return bytesToRead;
				}
			}
			
			this.mReadPos = 0;
			this.mReadLen = 0;
			int topUpBytes = count - bytesToRead;
			int bytesRead = 0;
			byte[] temp = new byte[topUpBytes];
			if (!m_CommAPI.ReadFile(hPort, temp, topUpBytes, ref bytesRead, this.mRxOverlapped)) {
				throw new ApplicationException("Read failed");
			}
			//			if (bytesRead != topUpBytes){
			//				//assert
			//			}
			Buffer.BlockCopy(temp, 0, buffer, offset + bytesToRead, bytesRead);
			this.mDecoder = null;
			return bytesToRead + bytesRead;
		}
		/// <summary>
		/// Synchronously reads one byte from the OpenNETCF.IO.Ports.SerialPort input buffer.
		/// </summary>
		/// <returns>The byte that was read.</returns>
		public int ReadByte() {
			if (!this.IsOpen) {
				throw new InvalidOperationException("Port is not open");
			}
			if (this.mReadLen != this.mReadPos) {
				return this.mInBuffer[this.mReadPos++];
			}
			mDecoder = null;
			byte[] temp = new byte[1];
			int one = this.Read(temp, 0, 1);
			return temp[0];
		}
		/// <summary>
		/// Reads up to the OpenNETCF.IO.Ports.SerialPort.NewLine value in the input buffer.
		/// </summary>
		/// <returns>A string containing the contents of the input buffer up to the OpenNETCF.IO.Ports.SerialPort.NewLine.</returns>
		public string ReadLine() {
			return this.ReadTo(this.NewLine);
		}
		/// <summary>
		/// Reads a number of bytes from the OpenNETCF.IO.Ports.SerialPort input buffer and writes those bytes into a character array at a given offset.
		/// </summary>
		/// <param name="buffer">The character array to which the input is written.</param>
		/// <param name="offset">The offset in the buffer array where writing should begin.</param>
		/// <param name="count">The number of bytes to be read.</param>
		/// <returns></returns>
		public int Read(char[] buffer, int offset, int count) {
			//TODO Read char[]
			throw new NotSupportedException("not yet");
		}
		/// <summary>
		/// Synchronously reads one character from the OpenNETCF.IO.Ports.SerialPort input buffer.
		/// </summary>
		/// <returns>The character read.</returns>
		public int ReadChar() {
			//TODO Read single char
			throw new NotSupportedException("not yet");
		}
		/// <summary>
		/// Reads a string up to the specified value in the input buffer.
		/// </summary>
		/// <param name="value">String value where the read operation stops.</param>
		/// <returns>A string containing the contents of the input buffer up to the value.</returns>
		public string ReadTo(string value) {
			//TODO read up to given string
			throw new NotSupportedException("not yet");
		}
		/// <summary>
		/// Reads all immediately available characters, based on the encoding, in both the stream and the input buffer of the OpenNETCF.IO.Ports.SerialPort object.
		/// </summary>
		/// <returns>A string composed of the contents of the stream and the input buffer of the OpenNETCF.IO.Ports.SerialPort object.</returns>
		public string ReadExisting() {
			//TODO read existing bytes and return string
			throw new NotSupportedException("not yet");
		}
		#endregion

		#region Write
		/// <summary>
		/// Writes a specified count of characters to an output buffer at the specified offset.
		/// </summary>
		/// <param name="buffer">The character array to which the output is written.</param>
		/// <param name="offset">The offset in the buffer array where writing should begin.</param>
		/// <param name="count">The number of characters to write.</param>
		public void Write(char[] buffer, int offset, int count) {
			byte[] bytesFromChars = this.Encoding.GetBytes(buffer, offset, count);
			this.Write(bytesFromChars, 0, bytesFromChars.Length);
		}
		/// <summary>
		/// Writes the parameter string to the output.
		/// </summary>
		/// <param name="str">The string for output.</param>
		public void Write(string str) {
			byte[] bytesFromString = this.mEncoding.GetBytes(str);
			this.Write(bytesFromString, 0, bytesFromString.Length);
		}
		/// <summary>
		/// Writes the specified string and the OpenNETCF.IO.Ports.SerialPort.NewLine value to the output buffer.
		/// </summary>
		/// <param name="str">The string to be written to output.</param>
		public void WriteLine(string str) {
			this.Write(str + this.NewLine);
		}
		/// <summary>
		/// Writes a specified count of bytes to an output buffer at the specified offset.
		/// </summary>
		/// <param name="buffer">The byte array to which the output is written.</param>
		/// <param name="offset">The offset in the buffer array where writing should begin.</param>
		/// <param name="count">The number of bytes to be write.</param>
		public void Write(byte[] buffer, int offset, int count) {
			if (!this.IsOpen) {
				throw new InvalidOperationException("Port is not open");
			}
			if (buffer == null) {
				throw new ArgumentNullException("buffer");
			}
			if (offset < 0) {
				throw new ArgumentOutOfRangeException("offset must be > 0");
			}
			if (count < 0) {
				throw new ArgumentOutOfRangeException("count must be > 0");
			}
			if ((buffer.Length - offset) < count) {
				throw new ArgumentException("FAILED: ((buffer.Length - offset) < count)");
			}
			if (buffer.Length == 0) {
				return;
			}

			//if in break don't write
			if (this.mInBreak){
				throw new ApplicationException("Can't write while in break");
			}

			byte[] temp = new byte[count];
			Buffer.BlockCopy(buffer, offset, temp, 0, count);

			//for desktop we should probably be doing other stuff here but if you are in .NET 2.0 you are not using this anyway
			int written = 0;
			if (!m_CommAPI.WriteFile(hPort, temp, count, ref written, this.mTxOverlapped)){
				int er = Marshal.GetLastWin32Error();
				if (er == 0x461){
					throw new ApplicationException("Write timed out 1");
				}
				throw new ApplicationException("writefile failed " + er);
			}

			if (written == 0){
				throw new ApplicationException("Write timed out 2");
			}
		}

		#endregion
		#endregion

		#region Privates
		private void CommEventThread() {
			CommEventFlags eventFlags = new CommEventFlags();
			AutoResetEvent rxevent = new AutoResetEvent(false);

			// specify the set of events to be monitored for the port.
			bool b;
			if(CommAPI.FullFramework) {
				b = m_CommAPI.SetCommMask(hPort, CommEventFlags.ALLPC);

				// set up the overlapped IO
				OVERLAPPED o = new OVERLAPPED();
				this.mRxOverlapped = LocalAlloc(0x40, Marshal.SizeOf(o));
				o.Offset = 0; 
				o.OffsetHigh = 0;
				o.hEvent = rxevent.Handle;
				Marshal.StructureToPtr(o, this.mRxOverlapped, true);
			}
			else {
				b = m_CommAPI.SetCommMask(hPort, CommEventFlags.ALLCE_2);
			}
			

			try {
				// let Open() know we're started
				this.mThreadStarted.Set();

				#region >>>> thread loop <<<<
				while(hPort != (IntPtr)CommAPI.INVALID_HANDLE_VALUE) {
					// wait for a Comm event
					if(!m_CommAPI.WaitCommEvent(hPort, ref eventFlags)) {
						int e = Marshal.GetLastWin32Error();

						if(e == (int)APIErrors.ERROR_IO_PENDING) {
							// IO pending so just wait and try again
							rxevent.WaitOne();
							Thread.Sleep(0);
							continue;
						}

						if(e == (int)APIErrors.ERROR_INVALID_HANDLE) {
							// Calling Port.Close() causes hPort to become invalid
							// Since Thread.Abort() is unsupported in the CF, we must
							// accept that calling Close will throw an error here.

							// Close signals the this.mCloseEvent, so wait on it
							// We wait 1 second, though Close should happen much sooner
							int eventResult = m_CommAPI.WaitForSingleObject(this.mCloseEvent, 1000);

							if(eventResult == (int)APIConstants.WAIT_OBJECT_0) {
								// the event was set so close was called
								hPort = (IntPtr)CommAPI.INVALID_HANDLE_VALUE;
					
								// reset our ResetEvent for the next call to Open
								this.mThreadStarted.Reset();

								if(this.mIsOpen) { // this should not be the case...if so, throw an exception for the owner
									string error = String.Format("Wait Failed: {0}", e);
									throw new ApplicationException(error);
								}

								return;
							}
						}

						// WaitCommEvent failed
						// 995 means an exit was requested (thread killed)
						if(e == 995) {
							return;
						}
						else {
							string error = String.Format("Wait Failed: {0}", e);
							throw new ApplicationException(error);
						}
					}

					// Re-specify the set of events to be monitored for the port.
					if(CommAPI.FullFramework) {
						m_CommAPI.SetCommMask(hPort, CommEventFlags.ALLPC);
					}
					else {
						m_CommAPI.SetCommMask(hPort, CommEventFlags.ALLCE);
					}
					// Process the flag - extracted main handling into its own method
					//ThreadPool.QueueUserWorkItem(new WaitCallback(ProcessEvents), eventFlags);					
					this.ProcessEvents(eventFlags);

				} // while(not invalid handle)
				#endregion
			} // try
			catch{
				if(this.mRxOverlapped != IntPtr.Zero) 
					LocalFree(this.mRxOverlapped);

				throw;
			}
		}
		private Decoder GetDecoder(){
			if (mDecoder == null){
				this.mDecoder = mEncoding.GetDecoder();			
			}
			return mDecoder;
		}

		private void ProcessEvents(object flags){
			CommEventFlags eventFlags = (CommEventFlags)flags;

			// check the event for errors
			#region >>>> error checking <<<<
			if(((uint)eventFlags & (uint)CommEventFlags.ERR) != 0) {
				CommErrorFlags errorFlags = new CommErrorFlags();
				CommStat commStat = new CommStat();

				// get the error status
				if(!m_CommAPI.ClearCommError(hPort, ref errorFlags, commStat)) {
					// ClearCommError failed!
					string error = String.Format("ClearCommError Failed: {0}", Marshal.GetLastWin32Error());
					throw new ApplicationException(error);
				}

				if(((uint)errorFlags & (uint)CommErrorFlags.BREAK) != 0) {
					// BREAK can set an error, so make sure the BREAK bit is set an continue
					eventFlags |= CommEventFlags.BREAK;
				}
				else {
					// we have an error.  Build a meaningful string and throw an exception
					if (ErrorReceived != null){
						if ((errorFlags & CommErrorFlags.TXFULL) != 0) {
							ErrorReceived(this,new SerialErrorReceivedEventArgs(SerialError.TXFull));	
						}
						if ((errorFlags & CommErrorFlags.RXOVER) != 0) {
							ErrorReceived(this,new SerialErrorReceivedEventArgs(SerialError.RXOver));	
						}
						if ((errorFlags & CommErrorFlags.OVERRUN) != 0) {
							ErrorReceived(this,new SerialErrorReceivedEventArgs(SerialError.Overrun));	
						}
						if ((errorFlags & CommErrorFlags.RXPARITY) != 0) {
							ErrorReceived(this,new SerialErrorReceivedEventArgs(SerialError.RXParity));	
						}
						if ((errorFlags & CommErrorFlags.FRAME) != 0) { 
							ErrorReceived(this,new SerialErrorReceivedEventArgs(SerialError.Frame));	
						}
					}
					return;
				}
			} // if(((uint)eventFlags & (uint)CommEventFlags.ERR) != 0)
			#endregion

			#region >>>> Receive data subsection <<<<
			// check for RXCHAR
			if (DataReceived != null){
				if((eventFlags & CommEventFlags.RXCHAR) != 0) {
					DataReceived(this,new SerialDataReceivedEventArgs(SerialData.Chars));
				}
				if(((uint)eventFlags & 2) != 0) {
					DataReceived(this,new SerialDataReceivedEventArgs(SerialData.Eof));
				}
			}
			#endregion

			#region >>>> line status checking <<<<
			if(PinChanged != null){
				// check the CTS
				if(((uint)eventFlags & (uint)CommEventFlags.CTS) != 0) {
					PinChanged(this,new SerialPinChangedEventArgs(SerialPinChange.CtsChanged));
				}

				// check the DSR
				if(((uint)eventFlags & (uint)CommEventFlags.DSR) != 0) {
					PinChanged(this,new SerialPinChangedEventArgs(SerialPinChange.DsrChanged));
				}
				
				// check for a RING
				if(((uint)eventFlags & (uint)CommEventFlags.RING) != 0) {
					PinChanged(this,new SerialPinChangedEventArgs(SerialPinChange.Ring));
				}

				// check for a RLSD
				if(((uint)eventFlags & (uint)CommEventFlags.RLSD) != 0) {
					PinChanged(this,new SerialPinChangedEventArgs(SerialPinChange.CDChanged));
				}

				// check for a break
				if(((uint)eventFlags & (uint)CommEventFlags.BREAK) != 0) {
					PinChanged(this,new SerialPinChangedEventArgs(SerialPinChange.Break));
				}
			}
			#endregion
		}

		private bool UpdateSettings() {
			if(!this.mIsOpen) return false;

			m_CommAPI.PurgeComm(hPort,0x4 | 0x8);

			bool outX = false;
			bool inX = false;
			bool outCts = false;
			byte rtsCtrl = 0x01;

			if (mHandshake != Handshake.None){			
				if (mHandshake == Handshake.RequestToSend || mHandshake == Handshake.RequestToSendXOnXOff){
					//outCts = true; by design
					rtsCtrl = 0x02;
				}else if (this.mRts == 0){
					rtsCtrl = 0x00;
				}
				if (mHandshake == Handshake.XOnXOff || mHandshake == Handshake.RequestToSendXOnXOff){
					outX = true;
					inX = true;
				}
			}

			// transfer the port settings to a DCB structure
			m_CommAPI.GetCommState(hPort, this.mDcb);
			this.mDcb.BaudRate = (uint)mBaudRate;
			this.mDcb.ByteSize = this.mByteSize;
			this.mDcb.EofChar = 0;// (sbyte)0x04;
			this.mDcb.ErrorChar = (sbyte)mErrorChar;
			this.mDcb.EvtChar = (sbyte)0x00;
			this.mDcb.fAbortOnError = false;
			this.mDcb.fBinary = true;
			this.mDcb.fDsrSensitivity = false;
			this.mDcb.fDtrControl = (byte)this.mDtr;
			this.mDcb.fErrorChar = (this.mDcb.ErrorChar != 0);
			this.mDcb.fInX = inX;
			this.mDcb.fNull = this.mDiscardNull;
			this.mDcb.fOutX = outX;
			this.mDcb.fOutxCtsFlow = outCts;
			this.mDcb.fOutxDsrFlow = false;
			this.mDcb.fParity = (mParity == Parity.None) ? false : true;
			this.mDcb.fRtsControl = rtsCtrl;
			this.mDcb.fTXContinueOnXoff = true;
			this.mDcb.Parity = (byte)mParity;
			this.mDcb.StopBits = (byte)this.mStopBits;
			this.mDcb.XoffChar = (sbyte)0x13; //ASCII.DC3;
			this.mDcb.XonChar = (sbyte)0x11; //ASCII.DC1;

			this.mDcb.XonLim = this.mDcb.XoffLim = 0;//(ushort)(this.mRxBufferSize / 10);

			// store some state variables
			this.mDtr = this.mDcb.fDtrControl == 0x01 ? 1 : 0;
			this.mRts = this.mDcb.fRtsControl == 0x01 ? 1 : 0;

			return m_CommAPI.SetCommState(hPort, this.mDcb);
		}

		private void UpdateTimeouts(){
			// set the Comm timeouts
			CommTimeouts ct = new CommTimeouts();

			// reading we'll return immediately
			// this doesn't seem to work as documented
			ct.ReadIntervalTimeout = 0xffffffff;
			if (this.mReadTimeout > 0){
				ct.ReadTotalTimeoutConstant = (uint)this.mReadTimeout;
				ct.ReadTotalTimeoutMultiplier = 0;
			}else{
				ct.ReadTotalTimeoutConstant = 0;
				ct.ReadTotalTimeoutMultiplier = 0;
			}

			uint writeTimeoutOrZero; 
			if (mWriteTimeout == InfiniteTimeout){
				writeTimeoutOrZero = 0;
			}else{
				writeTimeoutOrZero = (uint)mWriteTimeout; 
			}
			ct.WriteTotalTimeoutConstant = writeTimeoutOrZero;
			ct.WriteTotalTimeoutMultiplier = 0;

			m_CommAPI.SetCommTimeouts(hPort, ct);
		}

		[DllImport("kernel32", EntryPoint="LocalAlloc", SetLastError=true)]
		internal static extern IntPtr LocalAlloc(int uFlags, int uBytes);

		[DllImport("kernel32", EntryPoint = "LocalFree", SetLastError = true)]
		internal static extern IntPtr LocalFree(IntPtr hMem);

		#endregion
	}
}
