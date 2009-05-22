#if true
using System;
using System.Collections.Generic;
using System.Text;
using System.IO;
using InTheHand.Net;
using InTheHand.Net.Sockets;
using InTheHand.Net.Bluetooth;
using InTheHand.Net.Ports;
using System.Net.Sockets;
using System.IO.Ports;
using System.Runtime.InteropServices;
using System.Threading;

namespace BluetoothLayer
{
    public class BluetoothStream //: IDisposable
    {
        private static bool usingWidcomm;
        //all instances of BluetoothStream lock on this object
        private const int DEFAULT_READ_TIMEOUT = 100;//100 ms
        private const int DEFAULT_WRITE_TIMEOUT = 100;
        private const int MAX_TIMEOUTS = 10;//combined with 50 ms sleep time between reads, this amounts to .5 seconds with no data at all, very unlikely to happen normally

        private const int DEFAULT_BUFFER_SIZE = 10240;
        private static Predicate<DateTime> oldEnoughPredicate = new Predicate<DateTime>(isNewEnough);
        private static TimeSpan timeoutExceptionsOldnessCutoff = TimeSpan.FromSeconds(1);
        private static List<BluetoothStream> openStreams = new List<BluetoothStream>();
        //private static Thread readingThread = new Thread(new ThreadStart(readingLoop));
        private static Dictionary<BluetoothStream, int> timeouts = new Dictionary<BluetoothStream, int>();

        private List<DateTime> timeoutTimestamps;
        private Thread readingThread;

        #region MS_Stack_variables
        private BluetoothClient btClient;
        //private NetworkStream ms_stream;
        private Socket btSocket;
        private bool disposed = false;
        private byte[] localBuffer;
        //this is the buffer used to read asynchonously from the socket. When
        //the asynchronous read returns, this is copied into the localBuffer.
        private byte[] singleReadBuffer;
        private int head = 0;
        private int tail = 0;
        //signal from the asynchronous reading functions to the synchronous (external)
        //reading functions that the socket is dead and the stream should throw
        //an exception
        private bool socketDead = false;
        #endregion

        #region Widcomm_Stack_variables
        private string comPortName;
        private SerialPort comPort;
        #endregion

        static BluetoothStream()
        {
            usingWidcomm = BluetoothRadio.PrimaryRadio == null;
        }

        private BluetoothStream()
        {

        }

        ~BluetoothStream()
        {
            Dispose();
        }

        private void readingFunction()
        {
            while (!disposed)
            {
                if (usingWidcomm)
                {
                    throw new Exception("the reading thread shouldn't start when using the widcomm stack");
                }
                else
                {
                    if (!btClient.Connected)
                        return;

                    int bytesReceived = 0;
                    int currentBytes = tail - head;
                    if (currentBytes < 0)
                        currentBytes = DEFAULT_BUFFER_SIZE + currentBytes;

                    try
                    {
                        
                        bytesReceived = btSocket.Receive(singleReadBuffer, (DEFAULT_BUFFER_SIZE - currentBytes > singleReadBuffer.Length) ? singleReadBuffer.Length : DEFAULT_BUFFER_SIZE - currentBytes, SocketFlags.None);
                        
                    }
                    catch (Exception e)
                    {//just a debugging breakpoint. This never really gets thrown (in a disconnection scenario, at least)
                        throw e;
                    }

                    //this is a timeout. If we get too many of them, we classify that
                    //as a socket that has been disconnected
                    if (bytesReceived == 0)
                    {
                        List<DateTime> newTimeouts = timeoutTimestamps.FindAll(oldEnoughPredicate);
                        newTimeouts.Add(DateTime.Now);
                        if (newTimeouts.Count > MAX_TIMEOUTS)
                        {
                            socketDead = true;
                        }
                        timeoutTimestamps = newTimeouts;
                    }
                    Thread.Sleep(50);
                    
                    int ii;
                    for (ii = 0; ii < bytesReceived && ii < (DEFAULT_BUFFER_SIZE - currentBytes); ii++)
                    {
                        localBuffer[tail++] = singleReadBuffer[ii];
                        tail %= DEFAULT_BUFFER_SIZE;
                    }

                }

            }
        }

        /// <summary>
        /// Opens a Bluetooth connection with the specified address and returns
        /// a BluetoothStream object which can be used to communicate over that
        /// connection
        /// </summary>
        /// <param name="addr">The MAC address of the remote bluetooth device. 
        /// It <b>MUST</b> be in most-significant-byte first
        /// order (i.e. the bluetooth address 00:f1:ad:34:3d:f3 would be
        /// { 0x00, 0xf1, ...} and NOT {0xf3, 0x3d, ...})</param>
        /// <param name="pin">An optional pin for the bluetooth device</param>
        /// <returns></returns>
        public static BluetoothStream OpenConnection(byte[] addr, string pin)
        {
            BluetoothStream newStream = new BluetoothStream();
            try
            {
                if (usingWidcomm)
                {
                    IntPtr stringPtr = prepareCOMportWidcomm(addr);
                    if (stringPtr != IntPtr.Zero)
                        newStream.comPortName = Marshal.PtrToStringUni(stringPtr);
                    else
                        throw new Exception("Got a null pointer from the WIDCOMM code");

                    //now open the port
                    newStream.comPort = new SerialPort(newStream.comPortName);
                    newStream.comPort.Open();
                }
                else
                {
                    newStream.btClient = new BluetoothClient();
                    byte[] reverseAddr = new byte[addr.Length];
                    for (int ii = 0; ii < addr.Length; ii++)
                    {
                        reverseAddr[reverseAddr.Length - 1 - ii] = addr[ii];
                    }

                    newStream.timeoutTimestamps = new List<DateTime>();
                    newStream.localBuffer = new byte[DEFAULT_BUFFER_SIZE];
                    newStream.singleReadBuffer = new byte[DEFAULT_BUFFER_SIZE];
                    BluetoothRadio.PrimaryRadio.Mode = RadioMode.Connectable;
                    BluetoothAddress bt_addr = new BluetoothAddress(reverseAddr);
                    if (pin != null)
                        BluetoothSecurity.SetPin(bt_addr, pin);

                    newStream.btClient.Connect(bt_addr, BluetoothService.SerialPort);
                    newStream.btSocket = newStream.btClient.Client;
                    newStream.btSocket.Blocking = true;

                    newStream.readingThread = new Thread(new ThreadStart(newStream.readingFunction));
                    newStream.readingThread.Start();
                    
                }

            }
            catch
            {
                newStream.disposed = true;
                throw;
            }
            return newStream;
        }



        public int Read(byte[] destination, int offset, int length)
        {
            if (disposed)
                throw new ObjectDisposedException("BluetoothStream");

            if (usingWidcomm)
            {
                return comPort.Read(destination, offset, length);
            }
            else
            {
                if (socketDead)
                {
                    Dispose();
                    throw new Exception("socket is disconnected");
                }

                if (tail == head)
                    return 0;

                lock (this)
                {


                    int bytesCopied;
                    for (bytesCopied = 0; head != tail && bytesCopied < length; head = (head + 1) % DEFAULT_BUFFER_SIZE)
                    {
                        destination[bytesCopied + offset] = localBuffer[head];
                        bytesCopied++;
                    }
                    return bytesCopied;
                }
            }
        }

        public void Write(byte[] buffer, int offset, int length)
        {
            if (disposed)
                throw new ObjectDisposedException("BluetoothStream");
            try
            {
                if (usingWidcomm)
                {
                    comPort.Write(buffer, offset, length);
                }
                else
                {
                    //lock (lockObject)
                    btSocket.Send(buffer, offset, length, SocketFlags.None);//ms_stream.Write(buffer, offset, length);
                }
            }
            catch
            {
                Dispose();
                throw;
            }
        }

        public void Close()
        {
            Dispose();
        }

        private static bool isNewEnough(DateTime timestamp)
        {
            return DateTime.Now.Subtract(timestamp) < timeoutExceptionsOldnessCutoff;
        }


        [DllImport("WidcommWrapper.dll", CharSet = CharSet.Auto, EntryPoint = "?prepareCOMport@@YAPA_WQAE@Z")]
        private static extern IntPtr prepareCOMportWidcomm(byte[] addr);

        [DllImport("WidcommWrapper.dll", CharSet = CharSet.Auto, EntryPoint = "?instantiateBluetoothClient@@YAHXZ")]
        private static extern bool initializeWidcommBluetooth();

        [DllImport("WidcommWrapper.dll", CharSet = CharSet.Auto, EntryPoint = "?destroyBluetoothClient@@YAXXZ")]
        private static extern void destroyWidcommBluetooth();

        [DllImport("WidcommWrapper.dll", CharSet = CharSet.Auto, EntryPoint = "?setPin@@YAHQAEPA_W@Z")]
        private static extern bool setPinWidcomm(byte[] addr, String pin);

        public void Dispose()
        {
            lock (this)
            {
                if (disposed)
                    return;
                disposed = true;
            }
            if (readingThread != null)
                if (!readingThread.Join(500))
                    readingThread.Abort();

            if (usingWidcomm)
            {
                comPort.Close();
                comPort = null;
            }
            else
            {
                btSocket.Close();
                btClient.Close();
                btSocket = null;
                btClient = null;
            }

        }
    }
}
#endif
#if false
using System;
using System.Collections.Generic;
using System.Text;
using System.IO;
using InTheHand.Net;
using InTheHand.Net.Sockets;
using InTheHand.Net.Bluetooth;
using InTheHand.Net.Ports;
using System.Net.Sockets;
using System.IO.Ports;
using System.Runtime.InteropServices;
using System.Threading;

namespace BluetoothLayer
{
    public class BluetoothStream //: IDisposable
    {
        
        private static bool usingWidcomm;
        //all instances of BluetoothStream lock on this object
        private static object lockObject;
        private const int DEFAULT_READ_TIMEOUT = 100;//100 ms
        private const int DEFAULT_WRITE_TIMEOUT = 100;
        private const int MAX_TIMEOUTS = 10;//combined with 50 ms sleep time between reads, this amounts to .5 seconds with no data at all, very unlikely to happen normally

        private const int DEFAULT_BUFFER_SIZE = 1024;
        private static Predicate<DateTime> oldEnoughPredicate = new Predicate<DateTime>(isNewEnough);
        private static TimeSpan timeoutExceptionsOldnessCutoff = TimeSpan.FromSeconds(1);
        private static List<BluetoothStream> openStreams = new List<BluetoothStream>();
        //private static Thread readingThread = new Thread(new ThreadStart(readingLoop));
        private static Dictionary<BluetoothStream, int> timeouts = new Dictionary<BluetoothStream, int>();

        private List<DateTime> timeoutTimestamps;
        private Thread readingThread;

        #region MS_Stack_variables
        private BluetoothClient btClient;
        //private NetworkStream ms_stream;
        private Socket btSocket;
        private bool disposed = false;
        private byte[] localBuffer;
        //this is the buffer used to read asynchonously from the socket. When
        //the asynchronous read returns, this is copied into the localBuffer.
        private byte[] singleReadBuffer;
        private int head = 0;
        private int tail = 0;
        //signal from the asynchronous reading functions to the synchronous (external)
        //reading functions that the socket is dead and the stream should throw
        //an exception
        private bool socketDead = false;
        #endregion

        #region Widcomm_Stack_variables
        private string comPortName;
        private SerialPort comPort;
        #endregion

        static BluetoothStream()
        {
            usingWidcomm = BluetoothRadio.PrimaryRadio == null;
            lockObject = new object();
            
        }

        private BluetoothStream()
        {

        }

        ~BluetoothStream()
        {
            Dispose();
        }
        /*
        private void readingFunction()
        {
            while (!disposed)
            {
                if (usingWidcomm)
                {
                    //TODO FIXME
                }
                else
                {
                    if (!btClient.Connected)
                        return;

                    int bytesReceived = 0;
                    bool readHappened = false;
                    int currentBytes = tail - head;
                    if (currentBytes < 0)
                        currentBytes = DEFAULT_BUFFER_SIZE + currentBytes;
                    
                    try
                    {
                        if (btSocket.Available > 0)
                        {
                            readHappened = true;
                            lock (this)
                                lock (lockObject)
                                    bytesReceived = btSocket.Receive(singleReadBuffer, (DEFAULT_BUFFER_SIZE - currentBytes > singleReadBuffer.Length) ? singleReadBuffer.Length : DEFAULT_BUFFER_SIZE - currentBytes, SocketFlags.None);
                        }
                    }
                    catch (Exception e)
                    {
                        throw e;
                    }

                    //this is a timeout. If we get too many of them, we classify that
                    //as a socket that has been disconnected
                    if (readHappened && bytesReceived == 0)
                    {
                        List<DateTime> newTimeouts = timeoutTimestamps.FindAll(oldEnoughPredicate);
                        newTimeouts.Add(DateTime.Now);
                        if (newTimeouts.Count > MAX_TIMEOUTS)
                        {
                            socketDead = true;
                        }
                        timeoutTimestamps = newTimeouts;
                    }
                    Thread.Sleep(50);
                    //lock (this)
                    //{
                        
                        int ii;
                        for (ii = 0; ii < bytesReceived && ii < (DEFAULT_BUFFER_SIZE - currentBytes); ii++)
                        {
                            localBuffer[tail++] = singleReadBuffer[ii];
                            tail %= DEFAULT_BUFFER_SIZE;
                        }
                    /*
                        if (ii == DEFAULT_BUFFER_SIZE - currentBytes && ii < bytesReceived)
                        {
                            while (ii < bytesReceived)
                            {
                                localBuffer[tail++] = singleReadBuffer[ii++];
                                head++;
                                tail %= DEFAULT_BUFFER_SIZE;
                                head %= DEFAULT_BUFFER_SIZE;
                            }
                            head++;
                            head %= DEFAULT_BUFFER_SIZE;
                        }*/
                    //}
        /*
                }
                
            }
        }*/
        /*
        private static void readingLoop()
        {
            List<BluetoothStream> streamsToRemove = new List<BluetoothStream>();
            while (true)
            {

                foreach (BluetoothStream stream in openStreams)
                {
                    if (usingWidcomm)
                    {
                        //TODO FIXME
                    }
                    else
                    {
                        if (stream.btClient.Connected)
                        {
                            int bytesReceived;
                            try
                            {
                                bytesReceived = stream.btSocket.Receive(stream.singleReadBuffer);
                            }
                            catch (Exception e)
                            {
                                throw e;
                            }

                            //this is a timeout. If we get too many of them, we classify that
                            //as a socket that has been disconnected
                            if (bytesReceived == 0)
                            {
                                List<DateTime> newTimeouts = stream.timeoutTimestamps.FindAll(oldEnoughPredicate);
                                newTimeouts.Add(DateTime.Now);
                                if (newTimeouts.Count > MAX_TIMEOUTS)
                                {
                                    stream.socketDead = true;
                                    streamsToRemove.Add(stream);
                                }
                                stream.timeoutTimestamps = newTimeouts;
                            }

                            lock (stream)
                            {
                                int currentBytes = stream.tail - stream.head;
                                if (currentBytes < 0)
                                    currentBytes = DEFAULT_BUFFER_SIZE + currentBytes;
                                int ii;
                                for (ii = 0; ii < bytesReceived && ii < (DEFAULT_BUFFER_SIZE - currentBytes); ii++)
                                {
                                    stream.localBuffer[stream.tail++] = stream.singleReadBuffer[ii];
                                    stream.tail %= DEFAULT_BUFFER_SIZE;
                                }
                                if (ii == DEFAULT_BUFFER_SIZE - currentBytes && ii < bytesReceived)
                                {
                                    while (ii < bytesReceived)
                                    {
                                        stream.localBuffer[stream.tail++] = stream.singleReadBuffer[ii++];
                                        stream.head++;
                                        stream.tail %= DEFAULT_BUFFER_SIZE;
                                        stream.head %= DEFAULT_BUFFER_SIZE;
                                    }
                                    stream.head++;
                                    stream.head %= DEFAULT_BUFFER_SIZE;
                                }
                            }
                        }
                    }
                    
                }

                foreach (BluetoothStream stream in streamsToRemove)
                {
                    openStreams.Remove(stream);
                }
                streamsToRemove.Clear();
            }
        }
        */


        /// <summary>
        /// Opens a Bluetooth connection with the specified address and returns
        /// a BluetoothStream object which can be used to communicate over that
        /// connection
        /// </summary>
        /// <param name="addr">The MAC address of the remote bluetooth device. 
        /// It <b>MUST</b> be in most-significant-byte first
        /// order (i.e. the bluetooth address 00:f1:ad:34:3d:f3 would be
        /// { 0x00, 0xf1, ...} and NOT {0xf3, 0x3d, ...})</param>
        /// <param name="pin">An optional pin for the bluetooth device</param>
        /// <returns></returns>
        public static BluetoothStream OpenConnection(byte[] addr, string pin)
        {
            BluetoothStream newStream = new BluetoothStream();
            if (usingWidcomm)
            {
                IntPtr stringPtr = prepareCOMportWidcomm(addr);
                if (stringPtr != IntPtr.Zero)
                    newStream.comPortName = Marshal.PtrToStringUni(stringPtr);
                else
                    throw new Exception("Got a null pointer from the WIDCOMM code");

                //now open the port
                newStream.comPort = new SerialPort(newStream.comPortName);
                newStream.comPort.Open();
            }
            else
            {
                newStream.btClient = new BluetoothClient();
                byte[] reverseAddr = new byte[addr.Length];
                for (int ii = 0; ii < addr.Length; ii++)
                {
                    reverseAddr[reverseAddr.Length - 1 - ii] = addr[ii];
                }

                newStream.timeoutTimestamps = new List<DateTime>();
                newStream.localBuffer = new byte[DEFAULT_BUFFER_SIZE];
                newStream.singleReadBuffer = new byte[DEFAULT_BUFFER_SIZE];
                lock (lockObject) 
                {
                    BluetoothRadio.PrimaryRadio.Mode = RadioMode.Connectable;
                    BluetoothAddress bt_addr = new BluetoothAddress(reverseAddr);
                    if (pin != null)
                        BluetoothSecurity.SetPin(bt_addr, pin);

                    newStream.btClient.Connect(bt_addr, BluetoothService.SerialPort);
                    newStream.btSocket = newStream.btClient.Client;
                    newStream.btSocket.Blocking = true;
                    
                }
            }
            /*
            newStream.readingThread = new Thread(new ThreadStart(newStream.readingFunction));
            newStream.readingThread.Start();
             */
            return newStream;
        }

        
/*
        public int Read(byte[] destination, int offset, int length)
        {
            if (disposed)
                throw new ObjectDisposedException("BluetoothStream");

            try
            {
                if (usingWidcomm)
                {
                    return comPort.Read(destination, offset, length);
                }
                else
                {
                    if (socketDead)
                    {
                        Dispose();
                        throw new Exception("socket is disconnected");
                    }

                    if (tail == head)
                        return 0;

                    lock (this)
                    {
                    
                        
                        int bytesCopied;
                        for (bytesCopied = 0; head != tail && bytesCopied < length; head = (head + 1) % DEFAULT_BUFFER_SIZE)
                        {
                            destination[bytesCopied + offset] = localBuffer[head];
                            bytesCopied++;
                        }
                        return bytesCopied;
                        //return btSocket.Receive(destination, offset, length, SocketFlags.None);//ms_stream.Read(destination, offset, length);
                    }
                }
            }
            catch (SocketException socketEx) 
            {
                if (socketEx.ErrorCode == 10060)
                {
                    List<DateTime> recentEnoughTimeouts = timeoutTimestamps.FindAll(oldEnoughPredicate);
                    if (recentEnoughTimeouts.Count > MAX_TIMEOUTS)
                    {
                        Dispose();
                        throw new Exception("Excessive timeouts, probably a dead connection");
                    }
                    else
                    {
                        timeoutTimestamps = recentEnoughTimeouts;
                        timeoutTimestamps.Add(DateTime.Now);
                        return 0;
                    }
                }
                else
                {
                    throw socketEx;
                }
            }
            catch (Exception theException)
            {
                Dispose();
                throw theException;
            }
        }
 */
        public int Read(byte[] buffer, int offset, int length) 
        {
            if (disposed)
                throw new ObjectDisposedException("bluetoothStream");

            
            if (usingWidcomm)
            {
                return comPort.Read(buffer, offset, length);
            }
            else
            {
                if (btSocket.Available == 0)
                    return 0;
                lock (lockObject)
                    return btSocket.Receive(buffer, offset, length, SocketFlags.None);
            }
        }

        public void Write(byte[] buffer, int offset, int length)
        {
            if (disposed)
                throw new ObjectDisposedException("BluetoothStream");
            try
            {
                if (usingWidcomm)
                {
                    comPort.Write(buffer, offset, length);
                }
                else
                {
                    lock (lockObject)
                        btSocket.Send(buffer, offset, length, SocketFlags.None);//ms_stream.Write(buffer, offset, length);
                }
            }
            catch
            {
                Dispose();
                throw;
            }
        }

        public void Close()
        {
            Dispose();
        }
        
        private static bool isNewEnough(DateTime timestamp) 
        {
            return DateTime.Now.Subtract(timestamp) < timeoutExceptionsOldnessCutoff;
        }


        [DllImport("WidcommWrapper.dll", CharSet = CharSet.Auto, EntryPoint = "?prepareCOMport@@YAPA_WQAE@Z")]
        private static extern IntPtr prepareCOMportWidcomm(byte[] addr);

        [DllImport("WidcommWrapper.dll", CharSet = CharSet.Auto, EntryPoint = "?instantiateBluetoothClient@@YAHXZ")]
        private static extern bool initializeWidcommBluetooth();

        [DllImport("WidcommWrapper.dll", CharSet = CharSet.Auto, EntryPoint = "?destroyBluetoothClient@@YAXXZ")]
        private static extern void destroyWidcommBluetooth();

        [DllImport("WidcommWrapper.dll", CharSet = CharSet.Auto, EntryPoint = "?setPin@@YAHQAEPA_W@Z")]
        private static extern bool setPinWidcomm(byte[] addr, String pin);

        #region IDisposable Members

        public void Dispose()
        {
            lock (this)
            {
                if (disposed)
                    return;
                disposed = true;
            }

            //readingThread.Join();

            if (usingWidcomm)
            {
                //TODO FIXME
            }
            else
            {
                lock (lockObject)
                {
                    //ms_stream.Close();
                    btSocket.Close();
                    btClient.Close();
                    //ms_stream = null;
                    btSocket = null;
                    btClient = null;
                }
            }
            
        }

        #endregion
    }
}

#endif