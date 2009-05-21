using System;
using System.Collections.Generic;
using System.Collections;
using System.Text;
using System.Xml;
using System.IO;
using System.Net.Sockets;
using System.IO.Ports;
using HousenCS.SerialIO;
using System.Runtime.InteropServices;
using System.Threading;
using Wockets.Utils;
using System.Net;

#if (PocketPC)
using InTheHand.Net;
using InTheHand.Net.Sockets;
using InTheHand.Net.Bluetooth;
using InTheHand.Net.Ports;
#endif

namespace Wockets.Receivers
{
    public sealed class RFCOMMReceiver:SerialReceiver
    {
        #region Serialization Constants
        private const string RFCOMM_TYPE = "RFCOMM";      
        private const string MACADDRESS_ATTRIBUTE = "MacAddress";
        private const string PIN_ATTRIBUTE = "PIN";
        private const string TSNIFF_ATTRIBUTE = "TSniff";
        #endregion Serialization Constants
        //RFCOMM Configuration
        private const bool USE_PARITY = false;
        private const bool USE_STOP_BIT = true;
        private const int BAUD_RATE = 57600;
        private const int BUFFER_SIZE = 4096;
        private const int PORT_NUMBER = 9;
        private const int MAXIMUM_SAMPLING_RATE = 70;

        //RFCOMM Specific Objects
#if (PocketPC)
        private BluetoothStream bluetoothStream;
#endif
        private const int MAC_SIZE = 6;        
        private string address;
        private byte[] address_bytes;
        private string pin;
        private int sniffTime = 0;

        public RFCOMMReceiver()
        {
            this.type = ReceiverTypes.RFCOMM;            
        }
        /*
        public RFCOMMReceiver(string address,string pin)
            : base(BUFFER_SIZE, PORT_NUMBER, BAUD_RATE, USE_PARITY, USE_STOP_BIT,MAXIMUM_SAMPLING_RATE)
        {            
            this.address = address;
            this.address_bytes = new byte[MAC_SIZE];
            for (int i = 0; (i < MAC_SIZE); i++)
                this.address_bytes[i] = (byte)(System.Int32.Parse(address.Substring(i * 2, 2), System.Globalization.NumberStyles.AllowHexSpecifier) & 0xff);
            this.pin = pin;
        }
         */
        #region Access Properties
        public byte[] _AddressBytes
        {
            get
            {
                return this.address_bytes;
            }
        }
        public string _Address
        {
            get
            {
                return this.address;
            }
        }
        public string _PIN
        {
            get
            {
                return this.pin;
            }
        }

        public int _TSNIFF
        {
            get
            {
                return this.sniffTime;
            }

            set
            {
                this.sniffTime = value;
            }
        }
        #endregion Access Properties

        public override bool Initialize()
        {
            try
            {
#if (PocketPC)
                this.bluetoothStream = BluetoothStream.OpenConnection(this.address_bytes, this.pin);
#endif
                return true;
            }
            catch (Exception)
            {
                return false;
            }
        }

        public override int Read()
        {
           
           return  this.bluetoothStream.Read(this._Buffer, 0, this._Buffer.Length);
        }
        public override void Write(byte[] data, int length)
        {
            #if (PocketPC)
            this.bluetoothStream.Write(data, 0, length);
            #endif
        }
        public override bool Dispose()
        {
            try
            {
#if (PocketPC)
                this.bluetoothStream.Close();
#endif
                return true;
            }
            catch (Exception)
            {
                return false;
            }
        }

        #region Serialization Methods
        public override string ToXML()
        {
            string xml = "<"+RFCOMMReceiver.RECEIVER_ELEMENT+" ";
            xml += RFCOMMReceiver.ID_ATTRIBUTE + "=\"" + this._ID + "\" ";
            xml += RFCOMMReceiver.TYPE_ATTRIBUTE+"=\"" + RFCOMMReceiver.RFCOMM_TYPE + "\" ";
            xml += RFCOMMReceiver.MACADDRESS_ATTRIBUTE + "=\""+this.address+"\" ";
            xml += RFCOMMReceiver.PIN_ATTRIBUTE + "=\"" + this.pin + "\" ";
            xml += RFCOMMReceiver.TSNIFF_ATTRIBUTE + "=\"" + this.sniffTime + "\" ";
            xml += RFCOMMReceiver.PORT_NUMBER_ATTRIBUTE + "=\"" + this._PortNumber + "\" ";
            xml += RFCOMMReceiver.PARITY_ATTRIBUTE + "=\"" + this._Parity + "\" ";
            xml += RFCOMMReceiver.STOPBIT_ATTRIBUTE + "=\"" + this._StopBit + "\" ";
            xml += RFCOMMReceiver.BAUD_RATE_ATTRIBUTE + "=\"" + this._BaudRate + "\" ";
            xml += RFCOMMReceiver.BUFFERSIZE_ATTRIBUTE + "=\"" + this._Buffer.Length + "\" ";
            xml += RFCOMMReceiver.MAX_SR_ATTRIBUTE + "=\"" + this._MaximumSamplingRate + "\" ";
            xml += "/>";
            return xml;
        }
        public override void FromXML(string xml)
        {
            XmlDocument dom = new XmlDocument();
            dom.LoadXml(xml);
            XmlNode xNode = dom.DocumentElement;

            if ((xNode.Name == RFCOMMReceiver.RECEIVER_ELEMENT))
            {
                foreach (XmlAttribute xAttribute in xNode.Attributes)
                {

                    if ((xAttribute.Name == RFCOMMReceiver.TYPE_ATTRIBUTE) && (xAttribute.Value != RFCOMMReceiver.RFCOMM_TYPE))
                        throw new Exception("XML Parsing error - RFCOMM receiver parsing a receiver of a different type " + xAttribute.Value);  
                    else if (xAttribute.Name == RFCOMMReceiver.MACADDRESS_ATTRIBUTE)
                    {
                        this.address = xAttribute.Value;
                        this.address_bytes = new byte[MAC_SIZE];
                        for (int i = 0; (i < MAC_SIZE); i++)
                            this.address_bytes[i] = (byte)(System.Int32.Parse(address.Substring(i * 2, 2), System.Globalization.NumberStyles.AllowHexSpecifier) & 0xff);
                    }
                    else if (xAttribute.Name == RFCOMMReceiver.PIN_ATTRIBUTE)
                        this.pin = xAttribute.Value;
                    else if (xAttribute.Name == RFCOMMReceiver.PORT_NUMBER_ATTRIBUTE)
                        this._PortNumber = Convert.ToInt32(xAttribute.Value);
                    else if (xAttribute.Name == RFCOMMReceiver.TSNIFF_ATTRIBUTE)
                        this._TSNIFF = Convert.ToInt32(xAttribute.Value);
                    else if (xAttribute.Name == RFCOMMReceiver.PARITY_ATTRIBUTE)
                    {
                        if (xAttribute.Value == "true")
                            this._Parity = true;
                        else
                            this._Parity = false;
                    }
                    else if (xAttribute.Name == RFCOMMReceiver.STOPBIT_ATTRIBUTE)
                    {
                        if (xAttribute.Value == "true")
                            this._StopBit = true;
                        else
                            this._StopBit = false;
                    }
                    else if (xAttribute.Name == RFCOMMReceiver.BAUD_RATE_ATTRIBUTE)
                        this._BaudRate = Convert.ToInt32(xAttribute.Value);
                    else if (xAttribute.Name == RFCOMMReceiver.BUFFERSIZE_ATTRIBUTE)
                        this._Buffer = new byte[Convert.ToInt32(xAttribute.Value)];
                    else if (xAttribute.Name == RFCOMMReceiver.MAX_SR_ATTRIBUTE)
                        this._MaximumSamplingRate= Convert.ToInt32(xAttribute.Value);
                    else if (xAttribute.Name == RFCOMMReceiver.ID_ATTRIBUTE)
                        this._ID = Convert.ToInt32(xAttribute.Value);

                }
            }
        }
        #endregion Serialization Functions
    }


#if (PocketPC)
    internal class BluetoothStream //: IDisposable
    {
        private static bool usingWidcomm;
        //all instances of BluetoothStream lock on this object
        private static object lockObject;
        private const int DEFAULT_READ_TIMEOUT = 100;//100 ms
        private const int DEFAULT_WRITE_TIMEOUT = 100;
        private const int MAX_TIMEOUTS = 10;//combined with 50 ms sleep time between reads, this amounts to .5 seconds with no data at all, very unlikely to happen normally

        private const int DEFAULT_BUFFER_SIZE = 8000;
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
        private SerialPort sport;
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
        private SerialPortController comPort2;
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

        int prevData = 0;
        private TextWriter ttw = null;
        IntPtr cthread;

        private static int iii = 0;
        public static void Read_Callback(IAsyncResult ar)
        {
             
            //BluetoothStream so = ( BluetoothStream)ar.AsyncState;
            //so.bytesReceived= so.btSocket.EndReceive(ar);
            //so.receiving = false;
        }

        //public int bytesReceived = 0;
        //public bool receiving = false;
        private void readingFunction()
        {
            double prevTime = 0;
            double currentTime=0;
            double currentTime2 = 0;
            double prevTime2 = 0;
            int currentSamples = 0;
            byte[] buffer = new byte[100];


            localBuffer = new byte[DEFAULT_BUFFER_SIZE];
            singleReadBuffer = new byte[DEFAULT_BUFFER_SIZE];

            TextWriter tttw = new StreamWriter("samples"+(iii++)+".csv");
            NetworkStream n=btClient.GetStream();
            int counter = 0;
            bool tt=n.CanTimeout;
            

            while (!disposed)
            {
                if (usingWidcomm)
                {
                    //TODO FIXME
                }
                else
                {
                    //if (!comPort.IsOpen)
                      //  return;
                    if (!btClient.Connected)
                        return;

                    int bytesReceived = 0;
                    bool readHappened = false;
                    int currentBytes = tail - head;
                    if (currentBytes < 0)
                        currentBytes = DEFAULT_BUFFER_SIZE + currentBytes;



                    try
                    {
                        //if (btSocket.Available > 0)
                        //{
                        readHappened = true;
                        //lock (this)
                        //lock (lockObject)
                       //ArrayList listenList = new ArrayList();
                        //listenList.Add(btSocket);
                       // if (Socket.Select(null, null, listenList, 1000))
                        //    socketDead = true;
                        try
                        {
                            //Socket.Select(null, null,listenList, 10000);
                            //if (btSocket.Poll(-1,SelectMode.SelectRead))
                           //if (btSocket.Available>0)
                            //if (btSocket.Connected)

                                bytesReceived = btSocket.Receive(singleReadBuffer, (DEFAULT_BUFFER_SIZE - currentBytes > singleReadBuffer.Length) ? singleReadBuffer.Length : DEFAULT_BUFFER_SIZE - currentBytes, SocketFlags.None);
                            //int t = btSocket.Available;
                            //int x = n.ReadTimeout;
                            //byte[] alive=new byte[5];
                           /*
                            
                            if (t > 0)
                            {
                           
                                    bytesReceived = btSocket.Receive(singleReadBuffer, t, SocketFlags.None);                                
                                    counter = 0;
                                                                                     
                            }
                            else
                            {
                                bytesReceived = btSocket.Receive(singleReadBuffer, 0, SocketFlags.None);                                
                                if (counter > 2000)
                                {
                                    //int x = (int) btSocket.GetSocketOption(SocketOptionLevel.Socket, SocketOptionName.Error);
                                    socketDead = true;
                                    Close();
                                    return;

                                }
                                counter++;
                                Thread.Sleep(30);

                            }
                            */
                            
                            //btSocket. 
                             //bytesReceived = comPort2.FillBytesBuffer(singleReadBuffer);

                            currentTime = WocketsTimer.GetUnixTime();
                            currentTime2 = currentTime;
                            if (prevTime2 == 0)
                                prevTime2 = currentTime2;

                            //2 minutes passed
                            if ((prevTime2>0) && (currentTime2>0) && ((currentTime2 - prevTime2) >= 30000))
                            {

            /*                  
                                byte[] cmd = new byte[50];
                                for (int i=0;(i<50);i++)
                                    cmd[i] = (byte)36;                    
                                //SW,0640 1 sec
                                btSocket.Send(cmd, 50,SocketFlags.None);
                                Thread.Sleep(100);               
                                cmd[0] = (byte)'R';
                                cmd[1] = (byte)',';
                                cmd[2] = (byte)'1';                                
                                cmd[3] = (byte)13;
                                btSocket.Send(cmd, 4, SocketFlags.None); ;
                                Thread.Sleep(100);
                                prevTime2 = currentTime2;
                                socketDead = true;
             */
                                n.Close();
                                Close();
                                return;
                            }
    
                            /*
                            if ((currentTime - prevTime) < 500)
                                currentSamples += bytesReceived;
                            else
                            {
                                tttw.WriteLine(currentTime+"," + currentSamples/7);
                                currentSamples = 0;
                            }
                             */
                            prevTime = currentTime;
                            
                            
                        }
                        catch (Exception e)
                        {
                            socketDead = true;
                        }
                        
                      
                        //btSocket.BeginReceive(singleReadBuffer, (DEFAULT_BUFFER_SIZE - currentBytes > singleReadBuffer.Length) ? singleReadBuffer.Length : DEFAULT_BUFFER_SIZE - currentBytes,5, SocketFlags.None);
                        //btSocket.e
                        //if (!receiving)
                       //btSocket.BeginReceive(singleReadBuffer, (DEFAULT_BUFFER_SIZE - currentBytes > singleReadBuffer.Length) ? singleReadBuffer.Length : DEFAULT_BUFFER_SIZE - currentBytes,0 , SocketFlags.None, new AsyncCallback(Read_Callback), null);
                       //Thread.Sleep(10);
                       //bytesReceived=btSocket.EndReceive(null);

                        //}
                        //if ((prevData == 0) && (bytesReceived>0))
                
                        //Thread.Sleep(10);
                    }
                    catch (Exception e)
                    {
                        throw e;
                    }

                    //this is a timeout. If we get too many of them, we classify that
                    //as a socket that has been disconnected
                   /*
                    if (readHappened && bytesReceived == 0)
                    {
                        List<DateTime> newTimeouts = timeoutTimestamps.FindAll(oldEnoughPredicate);
                        newTimeouts.Add(DateTime.Now);
                        if (newTimeouts.Count > MAX_TIMEOUTS)
                        {
                            socketDead = true;
                        }
                        timeoutTimestamps = newTimeouts;
                    }*/
                   
                    //lock (this)
                    //{

                    int ii;
                    for (ii = 0; ii < bytesReceived && ii < (DEFAULT_BUFFER_SIZE - currentBytes); ii++)
                    {
                        localBuffer[tail++] = singleReadBuffer[ii];
                        //localBuffer[tail++] = buffer[ii++];
                        tail %= DEFAULT_BUFFER_SIZE;
                    }

                    //}

                }

            }
            tttw.Close();

        }

        // Bluetooth Parameters
        private static InTheHand.Net.BluetoothAddress blt_address;
        private static BluetoothClient blt;
        private static BluetoothEndPoint blt_endPoint;  
        private static int prevPort=1;
        public static string prepareCOMport(byte[] addr, string pin)
        {
            if (!usingWidcomm)
            {
                BluetoothRadio.PrimaryRadio.Mode = RadioMode.Connectable;
                byte[] reverseAddr = new byte[addr.Length];
                for (int ii = 0; ii < addr.Length; ii++)
                {
                    reverseAddr[reverseAddr.Length - 1 - ii] = addr[ii];
                }
                blt_address = new BluetoothAddress(reverseAddr);

                if (pin != null)
                    BluetoothSecurity.SetPin(blt_address, pin);

                blt_endPoint = new BluetoothEndPoint((BluetoothAddress)blt_address, BluetoothService.SerialPort);
                BluetoothSerialPort newPort = BluetoothSerialPort.CreateClient(blt_endPoint);
                /*BluetoothSerialPort newPort =null;
                
                for (int j = prevPort; (j < 100); j++)
                {
                    try
                    {
                        newPort = BluetoothSerialPort.CreateClient("COM"+j, blt_endPoint);
                        prevPort=j;
                        break;
                    }
                    catch (Exception)
                    {
                        continue;
                    }
                }*/

                if (newPort != null)
                    return newPort.PortName;
                else
                    throw new Exception("Got a null pointer from the Microsoft code");



            }
            else
            {
                IntPtr stringPtr = prepareCOMportWidcomm(addr);
                if (stringPtr != IntPtr.Zero)
                    return Marshal.PtrToStringUni(stringPtr);
                else
                    throw new Exception("Got a null pointer from the WIDCOMM code");
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
                    bool canStart = initializeWidcommBluetooth();
                    if (!canStart)
                        throw new Exception("Couldn't instantiate the Widcomm object in C++");
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

                    /*string comPortName = prepareCOMport(addr, "1234");
                    newStream.comPortName = comPortName;
                    newStream.comPort2 = new SerialPortController(true, false, 4096);//SerialPort(comPortName);
                    newStream.comPort2.SetPort(comPortName );
                    newStream.comPort2.SetBaudRate(19200);
                    newStream.comPort2.SetParity(0);
                    newStream.comPort2.SetStopBits(1);
                    newStream.comPort2.SetDCB();
              */
                    
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
                        /*

                        Microsoft.Win32.RegistryKey rkPorts = Microsoft.Win32.Registry.LocalMachine.OpenSubKey("SOFTWARE\\Microsoft\\Bluetooth\\Serial\\Ports", true);
                        Microsoft.Win32.RegistryKey rkNewPort = rkPorts.CreateSubKey(bt_addr.ToString("8"));                        
                        rkNewPort.SetValue("RemoteDCB", 0);
                        rkNewPort.SetValue("KeepDCD", 0);
                        rkNewPort.SetValue("Port", 0);
                      
                        rkNewPort.Close();

                        rkPorts.Close();
               
                         */

                        newStream.btClient.Connect(bt_addr, BluetoothService.SerialPort);                        
                        newStream.btSocket = newStream.btClient.Client;                      
                        newStream.btSocket.Blocking = true;

                    

                      

                        
                    }
                     
                    //byte[] addr1 = { 0x00, 0x06, 0x66, 0x01, 0xab, 0x4b };
       

                    /*for (int ii = 0; ii < 100; ii++)
                    {
                        if (!newStream.comPort2.)
                        {
                            try
                            {
                                newStream.comPort2.PortOpen();
                                break;
                            }
                            catch { continue; }
                        }
                    }*/
                }

                newStream.readingThread = new Thread(new ThreadStart(newStream.readingFunction));
                newStream.readingThread.Priority = ThreadPriority.Highest;
                newStream.readingThread.Start();

            }
            catch (Exception e)
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
                    //return btSocket.Receive(destination, offset, length, SocketFlags.None);//ms_stream.Read(destination, offset, length);
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
            ttw.Flush();
            ttw.Close();
        }

        private static bool isNewEnough(DateTime timestamp)
        {
            return DateTime.Now.Subtract(timestamp) < timeoutExceptionsOldnessCutoff;
        }

        //[DllImport("nk.dll")]
        //public static extern IntPtr GetCurrentThread();

        //[DllImport("coredll.dll", EntryPoint = "CeSetThreadPriority", SetLastError = true)]
        //public static extern bool CeSetThreadPriority(IntPtr hThread, int nPriority);


        //[DllImport("coredll.dll", EntryPoint = "CeGetThreadPriority", SetLastError = true)]
        //public static extern int CeGetThreadPriority(IntPtr hThread); 
     

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

            readingThread.Join();

            if (usingWidcomm)
            {
                //TODO FIXME
            }
            else
            {
                //lock (lockObject)
                //{
                //ms_stream.Close();
                btSocket.Close();
                btClient.Close();
                //ms_stream = null;
                btSocket = null;
                btClient = null;
                //}
            }

        }

        #endregion
    }
#endif
}
