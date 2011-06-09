using System;
using System.Runtime.InteropServices;
namespace Wockets.Utils.IPC.Queues
{
    public class P2PMessageQueue
    {

        #region Fields
        public const int TimeoutInfinite = -1;	// When waiting, sending or receiveing -1 means for ever
        public const int InfiniteQueueSize = 0;	// Used in construction for unlimited queue length
        private const int InvalidHandle = 0;	// Queue handle must be non-zero
        private const int DefaultMaxMsgLength = 4096; //you can change this default or override in the ctor
        private readonly bool mIsForReading = false;		// set at construction
        private readonly string mName = null;	// For named queues
        private IntPtr hQue = IntPtr.Zero;		// Handle to queue
        private byte[] mReadBuffer = null;		// Read buffer, reused in Receive methods
        #endregion

        #region DataOnQueueChanged Event
        /// <summary>
        /// For a read queue, raised when it is not empty
        /// For a write queue, raised when it is not full
        /// NOTE: Not applicable for Alert Messages!
        /// </summary>
        public event EventHandler DataOnQueueChanged;
        #endregion

        #region Read only properties
        /// <summary>
        /// Native handle to the queue.
        /// </summary>
        public IntPtr Handle
        {
            get
            {
                //Not needed but why close the door by not offering it!
                return hQue;
            }
        }

        /// <summary>
        /// true denotes a reading queue. 
        /// The return value will not change throught the lifetime of the object
        /// </summary>
        public bool CanRead
        {
            get
            {
                return mIsForReading;
            }
        }

        /// <summary>
        /// true denotes a writing queue. 
        /// The return value will not change throught the lifetime of the object
        /// </summary>
        public bool CanWrite
        {
            get
            {
                return !mIsForReading;
            }
        }

        /// <summary>
        /// Null or the name of a named queue 
        /// The return value will not change throught the lifetime of the object
        /// </summary>
        public string QueueName
        {
            get
            {
                return mName;
            }
        }

        /// <summary>
        /// Maximum number of messages allowed in queue, if it is zero, then no restriction on the number of messages.
        /// The return value will not change throught the lifetime of the object.
        /// </summary>
        public int MaxMessagesAllowed
        {
            get
            {
                return this.GetInfo().dwMaxMessages;
            }
        }

        /// <summary>
        /// Maximum length of a message in bytes.
        /// The return value will not change throught the lifetime of the object.
        /// </summary>
        public int MaxMessageLength
        {
            get
            {
                return this.GetInfo().cbMaxMessage;
            }
        }

        /// <summary>
        /// Maximum number of messages that have ever been in the queue at one time.
        /// </summary>
        public int MostMessagesSoFar
        {
            get
            {
                return this.GetInfo().dwMaxQueueMessages;
            }
        }

        /// <summary>
        /// Number of messages currently existing in the queue.
        /// Alert messages are not included in this count.
        /// </summary>
        public int MessagesInQueueNow
        {
            get
            {
                return this.GetInfo().dwCurrentMessages;
            }
        }

        /// <summary>
        /// Number of readers attached to the queue for reading.
        /// </summary>
        public short CurrentReaders
        {
            get
            {
                return this.GetInfo().wNumReaders;
            }
        }

        /// <summary>
        /// Number of writers attached to the queue for writing.
        /// </summary>
        public short CurrentWriters
        {
            get
            {
                return this.GetInfo().wNumWriters;
            }
        }
        #endregion

        #region creation | destruction
        // Called from OpenExisting
        private P2PMessageQueue(IntPtr hwnd, bool forReading)
        {
            if (hwnd.Equals(InvalidHandle))
            {
                throw new ApplicationException("Could not create queue, NativeError: " + Marshal.GetLastWin32Error());
            }
            hQue = hwnd;
            mIsForReading = forReading;

            this.StartEventThread();
        }

        /// <summary>
        /// Creates an unnamed queue with unlimited messages and message length.
        /// </summary>
        /// <param name="forReading">true for a read only queue; false for writing queue</param>
        public P2PMessageQueue(bool forReading) : this(forReading, null, DefaultMaxMsgLength, InfiniteQueueSize) { }

        /// <summary>
        /// Creates a named queue with unlimited messages and message length.
        /// </summary>
        /// <param name="forReading">true for a read only queue; false for writing queue</param>
        /// <param name="name">Name of queue</param>
        public P2PMessageQueue(bool forReading, string name) : this(forReading, name, DefaultMaxMsgLength, InfiniteQueueSize) { }

        /// <summary>
        /// Creates a named queue.
        /// </summary>
        /// <param name="forReading">true for a read only queue; false for writing queue</param>
        /// <param name="name">Name of queue</param>
        /// <param name="maxMessageLength">Maximum length of a message in bytes.</param>
        /// <param name="maxMessages">Maximum number of messages allowed in queue, if it is zero, then no restriction on the number of messages.</param>
        public P2PMessageQueue(bool forReading, string name, int maxMessageLength, int maxMessages)
        {
            if (name != null && name.Length > Win32Api.MAX_PATH)
            {
                throw new ApplicationException("name too long");
            }

            if (maxMessageLength < 0)
            {
                throw new ApplicationException("maxMessageLength must be positive");
            }

            if (maxMessages < 0)
            {
                throw new ApplicationException("maxMessages must be positive");
            }

            // setup options for creation
            Win32Api.MsgQueueOptions opt = new Win32Api.MsgQueueOptions(forReading, maxMessageLength, maxMessages);

            // configure queue behaviour
            opt.dwFlags = GetBehaviourFlag();

            try
            {
                hQue = Win32Api.CreateMsgQueue(name, opt);
            }
            catch (MissingMethodException ex)
            {
                // WinCE 4.x required
                throw new ApplicationException("P2P Queues are only supported by WinCE 4.x\r\n PPC2002 or other CE 3-based devices are not supported.", ex);
            }

            if (hQue.Equals(InvalidHandle))
            {
                throw new ApplicationException("Could not create queue " + name + ", NativeError: " + Marshal.GetLastWin32Error());
            }

            mIsForReading = forReading;
            mName = name;

            if (forReading)
            {
                this.mReadBuffer = new byte[maxMessageLength];
            }

            this.StartEventThread();
        }

        /// <summary>
        /// Creates a named queue.
        /// </summary>
        /// <param name="forReading">true for a read only queue; false for writing queue</param>
        /// <param name="name">Name of queue</param>
        /// <param name="maxMessageLength">Maximum length of a message in bytes.</param>
        /// <param name="maxMessages">Maximum number of messages allowed in queue, if it is zero, then no restriction on the number of messages.</param>
        /// <param name="createdNew">true, if named queue already existed, otherwise false</param>
        public P2PMessageQueue(bool forReading, string name, int maxMessageLength, int maxMessages, out bool createdNew)
            : this(forReading, name, maxMessageLength, maxMessages)
        {
            createdNew = (Marshal.GetLastWin32Error() != Win32Api.ERROR_ALREADY_EXISTS);
        }

        /// <summary>
        /// Frees all resources allocated by the queue. Do not use the object after this
        /// </summary>
        public void Close()
        {
            this.Dispose(false);
        }

        // Called from Close and the Finalizer
        private void Dispose(bool finalizing)
        {
            if (hQue.Equals(InvalidHandle))
            {
                return;
            }
            IntPtr toClose = hQue;
            hQue = IntPtr.Zero;
            Win32Api.CloseMsgQueue(toClose);
            if (!finalizing)
            {
                GC.SuppressFinalize(this);
            }
        }

        // Finalize
        ~P2PMessageQueue()
        {
            try
            {
                this.Dispose(true);
            }
            catch {/* just swallow any exception on shutdown */}
        }
        #endregion

        #region static OpenExisting
        /// <summary>
        /// Creates a new P2PMessageQueue based on the input parameters
        /// </summary>
        /// <param name="forReading">true for a read only queue; false for writing queue</param>
        /// <param name="processHandle">Native handle to a source process that owns the queueHandle message queue handle.</param>
        /// <param name="queueHandle">Native handle to a message queue returned by the CreateMsgQueue function or a P2PMessageQueue object.</param>
        /// <returns>a new P2PMessageQueue or null if the queue could not be opened</returns>
        public static P2PMessageQueue OpenExisting(bool forReading, IntPtr processHandle, IntPtr queueHandle)
        {
            IntPtr h = Win32Api.OpenMsgQueue(processHandle, queueHandle, new Win32Api.MsgQueueOptions(forReading));
            if (h.Equals(InvalidHandle))
            {
                return null;
            }
            P2PMessageQueue mq = new P2PMessageQueue(h, forReading);
            if (forReading)
            {
                mq.mReadBuffer = new byte[mq.MaxMessageLength];
            }
            return mq;
        }
        #endregion

        #region Read
        /// <summary>
        /// Reads the next message from the queue. Blocks until there is a message available.
        /// The queue must have been created with forReading = true.
        /// </summary>
        /// <param name="msg">The Message from the queue. Read its bytes if the result is OK.</param>
        /// <returns>a value from the ReadWriteResult enumeration</returns>
        public ReadWriteResult Receive(Message msg)
        {
            return this.Receive(msg, TimeoutInfinite);
        }

        /// <summary>
        /// Reads the next message from the queue.
        /// The queue must have been created with forReading = true.
        /// </summary>
        /// <param name="msg">The Message from the queue. Read its bytes if the result is OK.</param>
        /// <param name="ts">A timespan for which to wait for a message on the queue</param>
        /// <returns></returns>
        public ReadWriteResult Receive(Message msg, TimeSpan ts)
        {
            return this.Receive(msg, ts.Milliseconds);
        }


        /// <summary>
        /// Reads the next message from the queue.
        /// The queue must have been created with forReading = true.
        /// </summary>
        /// <param name="msg">The Message from the queue. Read its bytes if the result is OK.</param>
        /// <param name="timeoutMillis">a timeout in milliseconds for which to block (0 not to block at all). Use TimeoutInfinite to block until the queue has a message.</param>
        /// <returns>a value from the ReadWriteResult enumeration</returns>
        public ReadWriteResult Receive(Message msg, int timeoutMillis)
        {
            if (hQue.Equals(InvalidHandle))
            {
                throw new ApplicationException("Invalid Handle. Please use new queue");
            }

            int flags;
            int bytesRead;

            // We are re-using the mReadBuffer rather than create a new buffer each time. 
            // The implication is that the function is not thread safe (the whole class isn't but here it isn't by design)
            if (Win32Api.ReadMsgQueue(hQue, mReadBuffer, mReadBuffer.GetLength(0), out bytesRead, timeoutMillis, out flags))
            {
                byte[] dst = new byte[bytesRead];
                Buffer.BlockCopy(mReadBuffer, 0, dst, 0, bytesRead);
                msg.MessageBytes = dst;
                msg.IsAlert = (flags == Win32Api.MSGQUEUE_MSGALERT ? true : false);
                return ReadWriteResult.OK;

            }
            else
            {//Receive failed, get extended info and map it to our returned enum
                int err = Marshal.GetLastWin32Error();
                switch (err)
                {
                    case Win32Api.ERROR_INSUFFICIENT_BUFFER:
                        return ReadWriteResult.BufferFail;
                    case Win32Api.ERROR_PIPE_NOT_CONNECTED://no writers if NOT MSGQUEUE_ALLOW_BROKEN
                        return ReadWriteResult.Disconnected;
                    case Win32Api.ERROR_TIMEOUT:
                        return ReadWriteResult.Timeout;
                    case Win32Api.INVALID_HANDLE_ERROR: //This will happen if the caller was blocked on a Read and then subsequently closed the queue
                        this.Close();
                        return ReadWriteResult.InvalidHandle;
                    default:
                        throw new ApplicationException("Failed to read: " + err.ToString());
                }
            }
        }
        #endregion

        #region Send
        /// <summary>
        /// Adds a message to the queue (blocking if the queue is full).
        /// The queue must have been created with forReading = false.
        /// </summary>
        /// <param name="msg">The Message to send (contains the bytes)</param>
        /// <returns>a value from the ReadWriteResult enumeration</returns>
        public ReadWriteResult Send(Message msg)
        {
            return this.Send(msg, TimeoutInfinite);
        }

        /// <summary>
        /// Adds a message to the queue.
        /// The queue must have been created with forReading = false.
        /// </summary>
        /// <param name="msg">The Message to send (contains the bytes)</param>
        /// <param name="ts">The TimeSpan for which to wait until the queue is not full</param>
        /// <returns>a value from the ReadWriteResult enumeration</returns>
        public ReadWriteResult Send(Message msg, TimeSpan ts)
        {
            return this.Send(msg, ts.Milliseconds);
        }

        /// <summary>
        /// Adds a message to the queue.
        /// The queue must have been created with forReading = false.
        /// </summary>
        /// <param name="msg">The Message to send (contains the bytes)</param>
        /// <param name="timeoutMillis">a timeout in milliseconds for which to block (0 not to block at all). Use TimeoutInfinite to block until the queue is not full.</param>
        /// <returns>a value from the ReadWriteResult enumeration</returns>
        public ReadWriteResult Send(Message msg, int timeoutMillis)
        {
            if (hQue.Equals(InvalidHandle))
            {
                throw new ApplicationException("Invalid Handle. Please use new queue");
            }

            byte[] bytes = msg.MessageBytes;
            if (bytes == null)
            {
                throw new ApplicationException("Message must contain bytes");
            }
            if (Win32Api.WriteMsgQueue(hQue, bytes, bytes.GetLength(0), timeoutMillis, msg.IsAlert ? Win32Api.MSGQUEUE_MSGALERT : 0))
            {
                return ReadWriteResult.OK;
            }
            else
            {
                msg = null;
                int err = Marshal.GetLastWin32Error();
                switch (err)
                {
                    case Win32Api.ERROR_INSUFFICIENT_BUFFER:
                        return ReadWriteResult.BufferFail;
                    case Win32Api.ERROR_PIPE_NOT_CONNECTED://no readers if NOT MSGQUEUE_ALLOW_BROKEN
                        return ReadWriteResult.Disconnected;
                    case Win32Api.ERROR_TIMEOUT: //queue is full you get this
                        return ReadWriteResult.Timeout;
                    case Win32Api.ERROR_OUTOFMEMORY: //if MSGQUEUE_NOPRECOMMIT
                        return ReadWriteResult.Timeout;
                    case Win32Api.INVALID_HANDLE_ERROR:
                        this.Close();
                        return ReadWriteResult.InvalidHandle;
                    default:
                        throw new ApplicationException("Failed to write: " + err.ToString());
                }
            }
        }
        #endregion

        #region Purge
        /// <summary>
        /// Deletes all the messages contained in the queue.
        /// Applicable only for read queues (CanRead = true)
        /// </summary>
        public void Purge()
        {
            if (this.CanWrite)
            {
                throw new ApplicationException("Queue is write only. Purge not applicable");
            }

            if (hQue.Equals(InvalidHandle))
            {
                throw new ApplicationException("Invalid Handle. Please use new queue");
            }

            ReadWriteResult rwr = ReadWriteResult.OK;
            while (rwr == ReadWriteResult.OK)
            {
                Message msg = new Message();
                rwr = this.Receive(msg, 0);
            }
        }
        #endregion

        #region Private/Protected helper methods
        // On its own thread, monitors the queue handle and raises the DataOnQueueChanged event accordingly
        private void MonitorHandle()
        {
            int res;
            while (!hQue.Equals(InvalidHandle))
            {
                res = Win32Api.WaitForSingleObject(hQue, TimeoutInfinite);
                if (hQue.Equals(InvalidHandle) == true)
                {
                    return; // queue closed
                }
                if (res == Win32Api.WAIT_OBJECT_0)
                {
                    if (Win32Api.EventModify(hQue, (int)Win32Api.EventFlags.EVENT_RESET) == 0)
                    {
                        return; //queue closed
                    }
                    if (DataOnQueueChanged != null)
                    {
                        if (this.CanRead //catches the case where a writer gets created/closed
                                && this.MessagesInQueueNow > 0)
                        { //sideeffect: the event is not raised for Alert messages
                            DataOnQueueChanged(this, EventArgs.Empty);//queue not empty
                        }
                        else if (this.CanWrite)
                        {
                            DataOnQueueChanged(this, EventArgs.Empty);//queue not full
                        }
                    }
                }
                else
                {
                    return; //no point waiting on this handle anymore
                }
            }

        }

        // Helper function, called by the various properties
        private Win32Api.MsgQueueInfo GetInfo()
        {
            if (hQue.Equals(InvalidHandle))
            {
                throw new ApplicationException("Invalid Handle. Please use new queue");
            }

            Win32Api.MsgQueueInfo qi = new Win32Api.MsgQueueInfo();
            qi.dwSize = 28;
            if (Win32Api.GetMsgQueueInfo(hQue, ref qi))
            {
                return qi;
            }
            throw new ApplicationException("Failed to get queue info. NativeError = " + Marshal.GetLastWin32Error());
        }

        /// <summary>
        /// Starts the thread that is responsible for raising the DataOnQueueChanged event
        /// For efficiency, if the client is not going to be catching events, create a 
        /// subclass and override thie method with an empty body
        /// </summary>
        protected virtual void StartEventThread()
        {
            System.Threading.Thread t;
            t = new System.Threading.Thread(new System.Threading.ThreadStart(MonitorHandle));
            t.Start();
        }


        /// <summary>
        /// Sets the MsgQueueInfo.dwFlags. See the MSDN documentation for a detailed description.
        /// Inherit and override to change the hardcoded behaviour. Default MSGQUEUE_ALLOW_BROKEN
        /// </summary>
        /// <returns>0, MSGQUEUE_ALLOW_BROKEN or MSGQUEUE_NOPRECOMMIT</returns>
        protected virtual int GetBehaviourFlag()
        {
            //return 0;
            //return Win32Api.MSGQUEUE_NOPRECOMMIT;

            //allow readers|writers without writers|readers. Least management.
            //if you care you can always query CurrentWriters, CurrentReaders
            return Win32Api.MSGQUEUE_ALLOW_BROKEN;
            // If the MSGQUEUE_ALLOW_BROKEN flag is not specified and either the read or write exists, assuming a single read and writer, the queue will be deleted from memory and only the open handle to the queue will exist. 
            // The only option at this point is to close the remaining open handle and reopen the queue if necessary.
        }
        #endregion

        #region Win32Api class wrapping pinvoke/dllimport declaration
        private class Win32Api
        {
            public const int ERROR_ALREADY_EXISTS = 183;
            public const int MSGQUEUE_MSGALERT = 0x00000001;
            public const int ERROR_PIPE_NOT_CONNECTED = 233;
            public const int ERROR_INSUFFICIENT_BUFFER = 122;
            public const int MSGQUEUE_NOPRECOMMIT = 0x00000001;
            public const int MSGQUEUE_ALLOW_BROKEN = 0x00000002;
            public const int ERROR_OUTOFMEMORY = 14;
            public const int ERROR_TIMEOUT = 1460;
            public const int WAIT_TIMEOUT = 258;
            public const int WAIT_OBJECT_0 = 0;
            public const int MAX_PATH = 260;
            public const int INVALID_HANDLE_ERROR = 6;

            [DllImport("coredll.dll", SetLastError = true)]
            public static extern int WaitForSingleObject(IntPtr hHandle, int dwMilliseconds);

            public enum EventFlags
            {
                EVENT_PULSE = 1,
                EVENT_RESET = 2,
                EVENT_SET = 3
            }
            [DllImport("coredll.dll", SetLastError = true)]
            public static extern int EventModify(IntPtr hEvent, int function);

            [DllImport("coredll.dll", SetLastError = true)]
            public static extern bool CloseMsgQueue(IntPtr hMsgQ);

            [DllImport("coredll.dll", SetLastError = true)]
            public static extern IntPtr CreateMsgQueue(string lpszName, MsgQueueOptions lpOptions);

            [DllImport("coredll.dll", SetLastError = true)]
            public static extern bool GetMsgQueueInfo(IntPtr hMsgQ, ref MsgQueueInfo lpInfo);

            [DllImport("coredll.dll", SetLastError = true)]
            public static extern IntPtr OpenMsgQueue(IntPtr hSrcProc, IntPtr hMsgQ,
                MsgQueueOptions lpOptions);

            [DllImport("coredll.dll", SetLastError = true)]
            public static extern bool ReadMsgQueue(IntPtr hMsgQ, byte[] lpBuffer, Int32 cbBufferSize, out Int32 lpNumberOfBytesRead, Int32 dwTimeout, out Int32 pdwFlags);

            [DllImport("coredll.dll", SetLastError = true)]
            public static extern bool WriteMsgQueue(IntPtr hMsgQ, byte[] lpBuffer, Int32 cbDataSize, Int32 dwTimeout, Int32 dwFlags);

            public struct MsgQueueInfo
            {
                public Int32 dwSize;
                public Int32 dwFlags;
                public Int32 dwMaxMessages;
                public Int32 cbMaxMessage;
                public Int32 dwCurrentMessages;
                public Int32 dwMaxQueueMessages;
                public Int16 wNumReaders;
                public Int16 wNumWriters;
            }

            public class MsgQueueOptions
            {
                public MsgQueueOptions(bool forReading, int maxMessageLength, int maxMessages)
                {
                    bReadAccess = forReading ? 1 : 0;
                    dwMaxMessages = maxMessages;
                    cbMaxMessage = maxMessageLength;
                    dwSize = 20;
                }
                public MsgQueueOptions(bool forReading)
                {
                    bReadAccess = forReading ? 1 : 0;
                    dwSize = 20;
                }

                public Int32 dwSize;
                public Int32 dwFlags;
                public Int32 dwMaxMessages;
                public Int32 cbMaxMessage;
                public Int32 bReadAccess;
            }

        }
        #endregion
    }
}
