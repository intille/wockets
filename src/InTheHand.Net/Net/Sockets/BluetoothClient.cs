// 32feet.NET - Personal Area Networking for .NET
//
// InTheHand.Net.Sockets.BluetoothClient
// 
// Copyright (c) 2003-2008 In The Hand Ltd, All rights reserved.
// This source code is licensed under the In The Hand Community License - see License.txt

using System;
using System.Collections;
using System.IO;
using System.Net;
using System.Net.Sockets;
using System.Runtime.InteropServices;
using InTheHand.Net.Bluetooth;
using Microsoft.Win32;
using InTheHand.Runtime.InteropServices;
using System.Threading;

namespace InTheHand.Net.Sockets
{
    /// <summary>
    /// Provides client connections for Bluetooth network services.
    /// </summary>
    /// <remarks>This class currently only supports devices which use the Microsoft Bluetooth stack, devices which use the WidComm stack will not work.</remarks>
    public class BluetoothClient : IDisposable
    {
        private bool cleanedUp = false;
        private SocketOptionHelper m_optionHelper;

        #region Constructor
#if WinCE
        static BluetoothClient()
        {
            InTheHand.Net.PlatformVerification.ThrowException();
        }
#endif

        /// <summary>
        /// Creates a new instance of <see cref="BluetoothClient"/>.
        /// </summary>
        public BluetoothClient()
        {

            try
            {
                this.Client = new Socket(AddressFamily32.Bluetooth, SocketType.Stream, BluetoothProtocolType.RFComm);
                


                //byte[] ttt = BitConverter.GetBytes(5000);
                //                this.Client.SetSocketOption(BluetoothSocketOptionLevel.RFComm, SocketOptionName.KeepAlive, true);




                //this.Client.SetSocketOption(SocketOptionLevel.Socket, SocketOptionName., 1000);
            }
            catch (SocketException se)
            {
                throw new PlatformNotSupportedException("32feet.NET does not support the Bluetooth stack on this device.", se);
            }
            m_optionHelper = new SocketOptionHelper(this.Client);
        }
        /// <summary>
        /// Initializes a new instance of the <see cref="BluetoothClient"/> class and binds it to the specified local endpoint.
        /// </summary>
        /// <param name="localEP">The <see cref="BluetoothEndPoint"/> to which you bind the Bluetooth Socket.
        /// Only necessary on multi-radio system where you want to select the local radio to use.</param>
        public BluetoothClient(BluetoothEndPoint localEP)
            : this()
        {
            if (localEP == null)
            {
                throw new ArgumentNullException("localEP");
            }

            //bind to specific local endpoint
            this.Client.Bind(localEP);
        }

        internal BluetoothClient(Socket acceptedSocket)
        {
            this.Client = acceptedSocket;
            m_optionHelper = new SocketOptionHelper(this.Client);
        }

        #endregion


        #region Query Length

        //length of time for query
        private TimeSpan inquiryLength = new TimeSpan(0, 0, 10);

        /// <summary>
        /// Amount of time allowed to perform the query.
        /// </summary>
        /// <remarks>On Windows CE the actual value used is expressed in units of 1.28 seconds, so will be the nearest match for the value supplied.
        /// The default value is 10 seconds. The maximum is 60 seconds.</remarks>
        public TimeSpan InquiryLength
        {
            get
            {
                return inquiryLength;
            }
            set
            {
                if ((value.TotalSeconds > 0) && (value.TotalSeconds <= 60))
                {
                    inquiryLength = value;
                }
                else
                {
                    throw new ArgumentOutOfRangeException("QueryLength must be a positive timespan between 0 and 60 seconds.");
                }
            }
        }
        #endregion

        #region Discover Devices
        /// <summary>
        /// Discovers accessible Bluetooth devices and returns their names and addresses.
        /// </summary>
        /// <returns>An array of BluetoothDeviceInfo objects describing the devices discovered.</returns>
        public BluetoothDeviceInfo[] DiscoverDevices()
        {
            return DiscoverDevices(255, true, true, true);
        }

        /// <summary>
        /// Discovers accessible Bluetooth devices and returns their names and addresses.
        /// </summary>
        /// <param name="maxDevices">The maximum number of devices to get information about.</param>
        /// <returns>An array of BluetoothDeviceInfo objects describing the devices discovered.</returns>
        public BluetoothDeviceInfo[] DiscoverDevices(int maxDevices)
        {
            return DiscoverDevices(maxDevices, true, true, true);
        }

        /// <summary>
        /// Discovers accessible Bluetooth devices and returns their names and addresses.
        /// </summary>
        /// <param name="maxDevices">The maximum number of devices to get information about.</param>
        /// <param name="authenticated">True to return previously authenticated/paired devices.</param>
        /// <param name="remembered">True to return remembered devices.</param>
        /// <param name="unknown">True to return previously unknown devices.</param>
        /// <returns>An array of BluetoothDeviceInfo objects describing the devices discovered.</returns>
        public BluetoothDeviceInfo[] DiscoverDevices(int maxDevices, bool authenticated, bool remembered, bool unknown)
        {
            WqsOffset.AssertCheckLayout();
            CsaddrInfoOffsets.AssertCheckLayout();
            //
            int discoveredDevices = 0;
            ArrayList al = new ArrayList();

            int handle = 0;
            int lookupresult = 0;



#if WinCE
            if (unknown)
            {
#endif
                byte[] buffer = new byte[1024];
                BitConverter.GetBytes(WqsOffset.StructLength_60).CopyTo(buffer, WqsOffset.dwSize_0);
                BitConverter.GetBytes(WqsOffset.NsBth_16).CopyTo(buffer, WqsOffset.dwNameSpace_20);

                int bufferlen = buffer.Length;


                BTHNS_INQUIRYBLOB bib = new BTHNS_INQUIRYBLOB();
                bib.LAP = 0x9E8B33;

#if WinCE
                bib.length = Convert.ToInt16(inquiryLength.TotalSeconds / 1.28);
                bib.num_responses = Convert.ToInt16(maxDevices);
#else
                bib.length = Convert.ToByte(inquiryLength.TotalSeconds);
#endif
                GCHandle hBib = GCHandle.Alloc(bib, GCHandleType.Pinned);
                IntPtr pBib = hBib.AddrOfPinnedObject();

                BLOB b = new BLOB(8, pBib);


                GCHandle hBlob = GCHandle.Alloc(b, GCHandleType.Pinned);

                Marshal32.WriteIntPtr(buffer, WqsOffset.lpBlob_56, hBlob.AddrOfPinnedObject());


                //start looking for Bluetooth devices
                LookupFlags flags = LookupFlags.Containers;

#if WinXP
                //ensure cache is cleared on XP when looking for new devices
                if(unknown)
                {
                    flags |= LookupFlags.FlushCache;
                }
#endif
                lookupresult = NativeMethods.WSALookupServiceBegin(buffer, flags, out handle);

                hBlob.Free();
                hBib.Free();

                while (discoveredDevices < maxDevices && lookupresult != -1)
                {
#if WinCE
                    lookupresult = NativeMethods.WSALookupServiceNext(handle, LookupFlags.ReturnAddr | LookupFlags.ReturnBlob, ref bufferlen, buffer);
#else
                    lookupresult = NativeMethods.WSALookupServiceNext(handle, LookupFlags.ReturnAddr , ref bufferlen, buffer);
#endif

                    if (lookupresult != -1)
                    {
                        //increment found count
                        discoveredDevices++;


                        //status
#if WinXP
                        BTHNS_RESULT status = (BTHNS_RESULT)BitConverter.ToInt32(buffer, WqsOffset.dwOutputFlags_52);
                        bool devAuthd = ((status & BTHNS_RESULT.Authenticated) == BTHNS_RESULT.Authenticated);
                        bool devRembd = ((status & BTHNS_RESULT.Remembered) == BTHNS_RESULT.Remembered);
                        if (devAuthd && !devRembd) {
                            System.Diagnostics.Debug.WriteLine("Win32 BT disco: Auth'd but NOT Remembered.");
                        }
                        bool devUnkwn = !devRembd && !devAuthd;
                        bool include = (authenticated && devAuthd) || (remembered && devRembd) || (unknown && devUnkwn);
                        if (include)
#else
                        if (true)
#endif
                        {
#if WinCE
                            IntPtr lpBlob = (IntPtr)BitConverter.ToInt32(buffer, 56);
                            BLOB ib = (BLOB)Marshal.PtrToStructure(lpBlob, typeof(BLOB));
                            BthInquiryResult bir = (BthInquiryResult)Marshal.PtrToStructure(ib.pBlobData, typeof(BthInquiryResult));
#endif
                            //struct CSADDR_INFO {
                            //    SOCKET_ADDRESS LocalAddr;
                            //    SOCKET_ADDRESS RemoteAddr;
                            //    INT iSocketType;
                            //    INT iProtocol;
                            //}
                            //struct SOCKET_ADDRESS {
                            //    LPSOCKADDR lpSockaddr;
                            //    INT iSockaddrLength;
                            //}
                            //pointer to outputbuffer
                            IntPtr bufferptr = Marshal32.ReadIntPtr(buffer, WqsOffset.lpcsaBuffer_48);
                            //remote socket address
                            IntPtr sockaddrptr = Marshal32.ReadIntPtr(bufferptr, CsaddrInfoOffsets.OffsetRemoteAddr_lpSockaddr_8);
                            //remote socket len
                            int sockaddrlen = Marshal.ReadInt32(bufferptr, CsaddrInfoOffsets.OffsetRemoteAddr_iSockaddrLength_12);


                            SocketAddress btsa = new SocketAddress(AddressFamily32.Bluetooth, sockaddrlen);

                            for (int sockbyte = 0; sockbyte < sockaddrlen; sockbyte++)
                            {
                                btsa[sockbyte] = Marshal.ReadByte(sockaddrptr, sockbyte);
                            }

                            BluetoothEndPoint bep = new BluetoothEndPoint(null, BluetoothService.Empty);
                            bep = (BluetoothEndPoint)bep.Create(btsa);

                            //new deviceinfo
                            BluetoothDeviceInfo newdevice;

#if WinCE
                            newdevice = new BluetoothDeviceInfo(bep.Address, bir.cod);
#else
                            newdevice = new BluetoothDeviceInfo(bep.Address);
#endif
                            //add to discovered list
                            al.Add(newdevice);
                        }


                    }
                }
#if WinCE
            }
#endif

            //stop looking
            if (handle != 0)
            {
                lookupresult = NativeMethods.WSALookupServiceEnd(handle);
            }

#if WinCE

            //open bluetooth device key
            RegistryKey devkey = Registry.LocalMachine.OpenSubKey("Software\\Microsoft\\Bluetooth\\Device");
            bool addFromRegistry = authenticated || remembered;

            if (devkey != null)
            {

                //enumerate the keys
                foreach (string devid in devkey.GetSubKeyNames())
                {
                    BluetoothAddress address;

                    if (BluetoothAddress.TryParse(devid, out address))
                    {
                        //get friendly name
                        RegistryKey thisdevkey = devkey.OpenSubKey(devid);
                        string name = thisdevkey.GetValue("name", "").ToString();
                        uint classOfDevice = Convert.ToUInt32(thisdevkey.GetValue("class", 0));
                        thisdevkey.Close();

                        //add to collection
                        BluetoothDeviceInfo thisdevice = new BluetoothDeviceInfo(address, name, classOfDevice, true);

                        int devindex = al.IndexOf(thisdevice);

                        if (devindex == -1)
                        {
                            //if we intended to search for authenticated devices add this one to the collection
                            if (addFromRegistry)
                            {
                                al.Add(thisdevice);
                            }
                        }
                        else
                        {
                            if (addFromRegistry)
                            {
                                //set authenticated flag on existing discovered device
                                ((BluetoothDeviceInfo)al[devindex]).Authenticated = true;
                            }
                            else
                            {
                                //we want to exclude already authenticated devices so remove it from the collection
                                al.RemoveAt(devindex);
                            }
                        }
                    }
                }

                devkey.Close();
            }
#endif


            //return results
            if (al.Count == 0)
            {
                //special case for empty collection
                return new BluetoothDeviceInfo[0] { };
            }

            return (BluetoothDeviceInfo[])al.ToArray(typeof(BluetoothDeviceInfo));
        }
        #endregion



        #region Available
        /// <summary>
        /// Gets the amount of data that has been received from the network and is available to be read.
        /// </summary>
        /// <value>The number of bytes of data received from the network and available to be read.</value>
        /// <exception cref="ObjectDisposedException">The <see cref="Socket"/> has been closed.</exception>
        public int Available
        {
            get
            {
                return clientSocket.Available;
            }
        }
        #endregion

        #region Client

        private Socket clientSocket;

        /// <summary>
        /// Gets or sets the underlying <see cref="Socket"/>.
        /// </summary>
        public Socket Client
        {
            get
            {
                return clientSocket;
            }
            set
            {
                this.clientSocket = value;
            }

        }

        #endregion

        #region Connect

 
        private Exception socketexception;
        private ManualResetEvent TimeoutObject = new ManualResetEvent(false);


        public void CallBackMethod(IAsyncResult asyncresult)
        {
            //BluetoothClient btclient = asyncresult.AsyncState as BluetoothClient;
            //btclient.EndConnect(asyncresult);
            TimeoutObject.Set();
            Socket s = (Socket)asyncresult.AsyncState;
            if (!s.Connected)            
                s.EndConnect(asyncresult);
                         
        }


        public void Connect(BluetoothAddress address, Guid service, int timeoutMSec)
        {
   
            if (address == null)
            {
                throw new ArgumentNullException("address");
            }
            if (service == Guid.Empty)
            {
                throw new ArgumentNullException("service");
            }
            BluetoothEndPoint remoteEP = new BluetoothEndPoint(address, service);

            TimeoutObject.Reset();
            socketexception = null;
            if (cleanedUp)
            {
                throw new ObjectDisposedException(base.GetType().FullName);
            }
            if (remoteEP == null)
            {
                throw new ArgumentNullException("remoteEP");
            }
            clientSocket.BeginConnect(remoteEP, new AsyncCallback(CallBackMethod), clientSocket);
            if (TimeoutObject.WaitOne(timeoutMSec, false))
            {
                if (clientSocket.Connected)                
                    return;                
                else                
                    throw new Exception("Connection failed");                
            }
            else
            {
                clientSocket.Close();
                throw new TimeoutException("TimeOut Exception");
            }


        }
        /// <summary>
        /// Connects a client to a specified endpoint.
        /// </summary>
        /// <param name="remoteEP">A <see cref="BluetoothEndPoint"/> that represents the remote device.</param>
        public void Connect(BluetoothEndPoint remoteEP)
        {
            if (cleanedUp)
            {
                throw new ObjectDisposedException(base.GetType().FullName);
            }
            if (remoteEP == null)
            {
                throw new ArgumentNullException("remoteEP");
            }

            //clientSocket.SetSocketOption(BluetoothSocketOptionLevel.RFComm, BluetoothSocketOptionName.SE);
            //StartAuthenticator(remoteEP.Address);
            // byte[] link = new byte[32];          
            //BitConverter.GetBytes(80).CopyTo(link, 0);

            //byte[] opt = new byte[2];
            //opt[1] = 0xff;
            //opt[2] = 0x00;
            //clientSocket.SetSocketOption(BluetoothSocketOptionLevel.RFComm, BluetoothSocketOptionName.SetMtuMinimum, 23);
            //clientSocket.SetSocketOption(BluetoothSocketOptionLevel.RFComm, BluetoothSocketOptionName.s,255);

            //BitConverter.ToInt32(ttt, 0);
            // clientSocket.SetSocketOption(SocketOptionLevel.Socket, SocketOptionName.ReceiveTimeout, 200);

       
  
                //clientSocket
            
                clientSocket.Connect(remoteEP);
            
            //clientSocket.
  
            
            //int t = (int)clientSocket.GetSocketOption(BluetoothSocketOptionLevel.RFComm, BluetoothSocketOptionName.GetReceiveBuffer); //BitConverter.ToInt32(ttt, 0);

            //int t = (int)clientSocket.GetSocketOption(BluetoothSocketOptionLevel.RFComm, BluetoothSocketOptionName.GetReceiveBuffer); //BitConverter.ToInt32(ttt, 0);
            //this.m_optionHelper.EnterSniffMode();

            //allDone.Reset();
            // clientSocket.BeginConnect(remoteEP, new AsyncCallback(ConnectCallback1), clientSocket);
            //allDone.WaitOne();
            //clientSocket.
            //if (clientSocket.Connected)


            /*
            ushort sniff_mode_max = 0xffff;
            ushort sniff_mode_min = 0x0001;
            ushort sniff_attempt = 0x7fff;
            ushort sniff_timeout = 0x7fff;
            ushort sniff_interval = 0;
            ////}
            byte[] optl = new byte[5 * sizeof(ushort)];
            BitConverter.GetBytes(sniff_mode_max).CopyTo(optl, 0 * sizeof(ushort));
            BitConverter.GetBytes(sniff_mode_min).CopyTo(optl, 1 * sizeof(ushort));
            BitConverter.GetBytes(sniff_attempt).CopyTo(optl, 2 * sizeof(ushort));
            BitConverter.GetBytes(sniff_timeout).CopyTo(optl, 3 * sizeof(ushort));
            BitConverter.GetBytes(sniff_interval).CopyTo(optl, 4 * sizeof(ushort));

            clientSocket.SetSocketOption(BluetoothSocketOptionLevel.RFComm, BluetoothSocketOptionName..EnterSniffMode, optl);
            */

            //           int  max = (int)clientSocket.GetSocketOption(BluetoothSocketOptionLevel.RFComm, BluetoothSocketOptionName.GetMtuMaximum);
            //          int mtu=(int) clientSocket.GetSocketOption(BluetoothSocketOptionLevel.RFComm, BluetoothSocketOptionName.GetMtu);
            //       int min = (int)clientSocket.GetSocketOption(BluetoothSocketOptionLevel.RFComm, BluetoothSocketOptionName.GetMtuMinimum);
        }
        /// <summary>
        /// Connects the client to a remote Bluetooth host using the specified Bluetooth address and service identifier. 
        /// </summary>
        /// <param name="address">The <see cref="BluetoothAddress"/> of the host to which you intend to connect.</param>
        /// <param name="service">The service identifier to which you intend to connect.</param>
        public void Connect(BluetoothAddress address, Guid service)
        {
            if (address == null)
            {
                throw new ArgumentNullException("address");
            }
            if (service == Guid.Empty)
            {
                throw new ArgumentNullException("service");
            }
            BluetoothEndPoint point = new BluetoothEndPoint(address, service);
            this.Connect(point);


            //this.Connect(point, 1000);


        }

        #region Begin Connect
        /// <summary>
        /// Begins an asynchronous request for a remote host connection.
        /// The remote host is specified by a <see cref="BluetoothAddress"/> and a service identifier (Guid). 
        /// </summary>
        /// <param name="address">The <see cref="BluetoothAddress"/> of the remote host.</param>
        /// <param name="service">The service identifier of the remote host.</param>
        /// <param name="requestCallback">An AsyncCallback delegate that references the method to invoke when the operation is complete.</param>
        /// <param name="state">A user-defined object that contains information about the connect operation.
        /// This object is passed to the requestCallback delegate when the operation is complete.</param>
        /// <returns></returns>
        public IAsyncResult BeginConnect(BluetoothAddress address, Guid service, AsyncCallback requestCallback, object state)
        {
            return BeginConnect(new BluetoothEndPoint(address, service), requestCallback, state);
        }

        /// <summary>
        /// Begins an asynchronous request for a remote host connection.
        /// The remote host is specified by a <see cref="BluetoothEndPoint"/>. 
        /// </summary>
        /// <param name="remoteEP">A <see cref="BluetoothEndPoint"/> containing the 
        /// address and UUID of the remote service.</param>
        /// <param name="requestCallback">An AsyncCallback delegate that references the method to invoke when the operation is complete.</param>
        /// <param name="state">A user-defined object that contains information about the connect operation.
        /// This object is passed to the requestCallback delegate when the operation is complete.</param>
        /// <returns></returns>
        public IAsyncResult BeginConnect(BluetoothEndPoint remoteEP, AsyncCallback requestCallback, object state)
        {
            //StartAuthenticator(remoteEP.Address);
            return this.Client.BeginConnect(remoteEP, requestCallback, state);
        }
        #endregion

        #region End Connect
        /// <summary>
        /// Asynchronously accepts an incoming connection attempt.
        /// </summary>
        /// <param name="asyncResult">An <see cref="IAsyncResult"/> object returned by a call to 
        /// <see cref="M:BeginConnect(InTheHand.Net.Sockets.BluetoothEndPoint,System.AsyncCallback,System.Object)"/>
        /// / <see cref="M:BeginConnect(InTheHand.Net.Sockets.BluetoothAddress,System.Guid,System.AsyncCallback,System.Object)"/>.
        /// </param>
        public void EndConnect(IAsyncResult asyncResult)
        {
            this.Client.EndConnect(asyncResult);
        }
        #endregion

        #endregion

        #region Connected
        /// <summary>
        /// Gets a value indicating whether the underlying <see cref="Socket"/> for a <see cref="BluetoothClient"/> is connected to a remote host.
        /// </summary>
        /// <value>true if the <see cref="Client"/> socket was connected to a remote resource as of the most recent operation; otherwise, false.</value>
        public bool Connected
        {
            get
            {
                return clientSocket.Connected;
            }
        }
        #endregion

        #region Close
        /// <summary>
        /// Closes the <see cref="BluetoothClient"/> and the underlying connection.
        /// </summary>
        /// -
        /// <remarks>The two XxxxxClient classes produced by Microsoft (TcpClient, 
        /// and IrDAClient in the NETCF) have had various documented behaviours and various
        /// actual behaviours for close/dispose/finalize on the various platforms. :-(
        /// The current TcpClient implementation on is that 
        /// Close/Dispose closes the connection by closing the underlying socket and/or
        /// NetworkStream, and finalization doesn't close either.  This is the behaviour
        /// we use for the here (for <see cref="T:InTheHand.Net.Sockets.BluetoothClient"/>,
        /// <see cref="T:InTheHand.Net.Sockets.IrDAClient"/>).  (The documentation in MSDN for 
        /// <see cref="T:System.Net.Sockets.TcpClient"/> is still wrong by-the-way,
        /// see <see href="https://connect.microsoft.com/VisualStudio/feedback/ViewFeedback.aspx?FeedbackID=158480">
        /// Microsoft feedback #158480</see>).
        /// </remarks>
        public void Close()
        {
            Dispose();

        }
        #endregion

        #region Get Stream

        private NetworkStream dataStream;

        /// <summary>
        /// Gets the underlying stream of data.
        /// </summary>
        /// <returns>The underlying <see cref="NetworkStream"/>.</returns>
        /// <remarks><see cref="GetStream"/> returns a <see cref="NetworkStream"/> that you can use to send and receive data.
        /// The <see cref="NetworkStream"/> class inherits from the <see cref="Stream"/> class, which provides a rich collection of methods and properties used to facilitate network communications.
        /// <para>You must call the <see cref="Connect(InTheHand.Net.BluetoothEndPoint)"/> / <see cref="M:Connect(InTheHand.Net.BluetoothAddress,System.Guid)"/>
        /// method first, or the <see cref="GetStream"/> method will throw an <see cref="InvalidOperationException"/>.
        /// After you have obtained the <see cref="NetworkStream"/>, call the <see cref="NetworkStream.Write"/> method to send data to the remote host.
        /// Call the <see cref="NetworkStream.Read"/> method to receive data arriving from the remote host.
        /// Both of these methods block until the specified operation is performed.
        /// You can avoid blocking on a read operation by checking the <see cref="NetworkStream.DataAvailable"/> property.
        /// A true value means that data has arrived from the remote host and is available for reading.
        /// In this case, <see cref="NetworkStream.Read"/> is guaranteed to complete immediately.
        /// If the remote host has shutdown its connection, <see cref="NetworkStream.Read"/> will immediately return with zero bytes.</para></remarks>
        /// <exception cref="InvalidOperationException">The <see cref="BluetoothClient"/> is not connected to a remote host.</exception>
        /// <exception cref="ObjectDisposedException">The <see cref="BluetoothClient"/> has been closed.</exception>
        public NetworkStream GetStream()
        {
            if (cleanedUp)
            {
                throw new ObjectDisposedException(base.GetType().FullName);
            }
            if (!this.Client.Connected)
            {
                throw new InvalidOperationException("The operation is not allowed on non-connected sockets.");
            }

            if (dataStream == null)
            {
                dataStream = new NetworkStream(this.Client, true);

            }


            return dataStream;
        }
        #endregion


        #region Authenticate
        /// <summary>
        /// Gets or sets the authentication state of the current connect or behaviour to use when connection is established.
        /// </summary>
        /// <remarks>
        /// For disconnected sockets, specifies that authentication is required in order for a connect or accept operation to complete successfully.
        /// Setting this option actively initiates authentication during connection establishment, if the two Bluetooth devices were not previously authenticated.
        /// The user interface for passkey exchange, if necessary, is provided by the operating system outside the application context.
        /// For outgoing connections that require authentication, the connect operation fails with WSAEACCES if authentication is not successful.
        /// In response, the application may prompt the user to authenticate the two Bluetooth devices before connection.
        /// For incoming connections, the connection is rejected if authentication cannot be established and returns a WSAEHOSTDOWN error.
        /// </remarks>
        public bool Authenticate
        {
            get { return m_optionHelper.Authenticate; }
            set { m_optionHelper.Authenticate = value; }
        }
        #endregion

        #region Encrypt
        /// <summary>
        /// On unconnected sockets, enforces encryption to establish a connection.
        /// Encryption is only available for authenticated connections.
        /// For incoming connections, a connection for which encryption cannot be established is automatically rejected and returns WSAEHOSTDOWN as the error.
        /// For outgoing connections, the connect function fails with WSAEACCES if encryption cannot be established.
        /// In response, the application may prompt the user to authenticate the two Bluetooth devices before connection.
        /// </summary>
        public bool Encrypt
        {
            get { return m_optionHelper.Encrypt; }
            set { m_optionHelper.Encrypt = value; }
        }
        #endregion


        #region Link Key
        /// <summary>
        /// Returns link key associated with peer Bluetooth device.
        /// </summary>
        public Guid LinkKey
        {
            get
            {
                byte[] link = clientSocket.GetSocketOption(BluetoothSocketOptionLevel.RFComm, BluetoothSocketOptionName.GetLink, 32);

                byte[] bytes = new byte[16];
                Buffer.BlockCopy(link, 16, bytes, 0, 16);
                return new Guid(bytes);
            }
        }
        #endregion

        #region Link Policy
        /// <summary>
        /// Returns the Link Policy of the current connection.
        /// </summary>
        public LinkPolicy LinkPolicy
        {
            get
            {
                byte[] policy = clientSocket.GetSocketOption(BluetoothSocketOptionLevel.RFComm, BluetoothSocketOptionName.GetLinkPolicy, 4);
                return (LinkPolicy)BitConverter.ToInt32(policy, 0);
            }
        }

        public IntPtr GetSocketHandle()
        {
            return clientSocket.Handle;
        }
        #endregion


        #region Set PIN
        /// <summary>
        /// Sets the PIN associated with the currently connected device.
        /// </summary>
        /// <param name="pin">PIN which must be composed of 1 to 16 ASCII characters.</param>
        /// <remarks>Assigning null (Nothing in VB) or an empty String will revoke the PIN.</remarks>
        public void SetPin(string pin)
        {
            m_optionHelper.SetPin(((BluetoothEndPoint)clientSocket.RemoteEndPoint).Address, pin);
        }

        /// <summary>
        /// Set or change the PIN to be used with a specific remote device.
        /// </summary>
        /// <param name="device">Address of Bluetooth device.</param>
        /// <param name="pin">PIN string consisting of 1 to 16 ASCII characters.</param>
        /// <remarks>Assigning null (Nothing in VB) or an empty String will revoke the PIN.</remarks>
        public void SetPin(BluetoothAddress device, string pin)
        {
            m_optionHelper.SetPin(device, pin);
        }
        #endregion


        #region Remote Machine Name
        /// <summary>
        /// Gets the name of the remote device.
        /// </summary>
        public string RemoteMachineName
        {
            get
            {
                return GetRemoteMachineName(clientSocket);
            }
        }

        /// <summary>
        /// Gets the name of the specified remote device.
        /// </summary>
        /// <param name="a">Address of remote device.</param>
        /// <returns>Friendly name of specified device.</returns>
        public string GetRemoteMachineName(BluetoothAddress a)
        {
#if WinXP
            BluetoothDeviceInfo bdi = new BluetoothDeviceInfo(a);
            return bdi.DeviceName;
#else
            byte[] buffer = new byte[504];
            //copy remote device address to buffer
            Buffer.BlockCopy(a.ToByteArray(), 0, buffer, 0, 6);

            try
            {
                clientSocket.SetSocketOption(BluetoothSocketOptionLevel.RFComm, BluetoothSocketOptionName.ReadRemoteName, buffer);
                string name = string.Empty;
                name = System.Text.Encoding.Unicode.GetString(buffer, 8, 496);

                int offset = name.IndexOf('\0');
                if (offset > -1)
                {
                    name = name.Substring(0, offset);
                }

                return name;
            }
            catch (SocketException ex)
            {
                System.Diagnostics.Debug.WriteLine("BluetoothClient GetRemoteMachineName(addr) ReadRemoteName failed: " + ex.Message);
                return null;
            }
#endif
        }

        /// <summary>
        /// Gets the name of a device by a specified socket.
        /// </summary>
        /// <param name="s"> A <see cref="Socket"/>.</param>
        /// <returns>Returns a string value of the computer or device name.</returns>
        public static string GetRemoteMachineName(Socket s)
        {
#if WinXP
            BluetoothDeviceInfo bdi = new BluetoothDeviceInfo(((BluetoothEndPoint)s.RemoteEndPoint).Address);
            return bdi.DeviceName;
#else
            byte[] buffer = new byte[504];
            //copy remote device address to buffer
            Buffer.BlockCopy(((BluetoothEndPoint)s.RemoteEndPoint).Address.ToByteArray(), 0, buffer, 0, 6);

            string name = "";

            try
            {
                s.SetSocketOption(BluetoothSocketOptionLevel.RFComm, BluetoothSocketOptionName.ReadRemoteName, buffer);
                name = System.Text.Encoding.Unicode.GetString(buffer, 8, 496);

                int offset = name.IndexOf('\0');
                if (offset > -1)
                {
                    name = name.Substring(0, offset);
                }

                return name;
            }
            catch (SocketException ex)
            {
                System.Diagnostics.Debug.WriteLine("BluetoothClient GetRemoteMachineName(socket) ReadRemoteName failed: " + ex.Message);
                return null;
            }
#endif
        }
        #endregion

        #region IDisposable Members

        /// <summary>
        /// Releases the unmanaged resources used by the BluetoothClient and optionally releases the managed resources.
        /// </summary>
        /// <param name="disposing">true to release both managed and unmanaged resources; false to release only unmanaged resources.</param>
        protected virtual void Dispose(bool disposing)
        {
            if (!cleanedUp)
            {
                if (disposing)
                {
                    IDisposable idStream = dataStream;
                    if (idStream != null)
                    {
                        //dispose the stream which will also close the socket
                        idStream.Dispose();
                    }
                    else
                    {
                        if (this.Client != null)
                        {
                            this.Client.Close();
                            this.Client = null;
                        }
                    }
                }

                cleanedUp = true;
         
            }
        }

        /// <summary>
        /// Closes the <see cref="BluetoothClient"/> and the underlying connection.
        /// </summary>
        /// -
        /// <seealso cref="M:InTheHand.Net.Sockets.BluetoothClient.Close"/>
        public void Dispose()
        {
            Dispose(true);
            GC.SuppressFinalize(this);
        }

        /// <summary>
        /// Frees resources used by the <see cref="BluetoothClient"/> class.
        /// </summary>
        ~BluetoothClient()
        {
            Dispose(false);
        }

        #endregion

        #region Throw SocketException For HR
        internal static void ThrowSocketExceptionForHR(int errorCode)
        {
            if (errorCode < 0)
            {
                int socketerror = 0;
                socketerror = Marshal.GetLastWin32Error();

                throw new SocketException(socketerror);
            }
        }

        internal static void ThrowSocketExceptionForHrExceptFor(int errorCode, params int[] nonErrorCodes)
        {
            if (errorCode < 0)
            {
                int socketerror = 0;
                socketerror = Marshal.GetLastWin32Error();
                if (-1 != Array.IndexOf(nonErrorCodes, socketerror, 0, nonErrorCodes.Length))
                {
                    return;
                }
                throw new SocketException(socketerror);
            }
        }
        #endregion

        internal class SocketOptionHelper
        {
            readonly Socket m_socket;
#if ! WinCE
            private bool authenticate = false;
            private BluetoothWin32Authentication m_authenticator;
        
#endif
            private bool encrypt = false;

            internal SocketOptionHelper(Socket socket)
            {
                m_socket = socket;
            }

            #region Authenticate
            /// <summary>
            /// Gets or sets the authentication state of the current connect or behaviour to use when connection is established.
            /// </summary>
            /// <remarks>
            /// For disconnected sockets, specifies that authentication is required in order for a connect or accept operation to complete successfully.
            /// Setting this option actively initiates authentication during connection establishment, if the two Bluetooth devices were not previously authenticated.
            /// The user interface for passkey exchange, if necessary, is provided by the operating system outside the application context.
            /// For outgoing connections that require authentication, the connect operation fails with WSAEACCES if authentication is not successful.
            /// In response, the application may prompt the user to authenticate the two Bluetooth devices before connection.
            /// For incoming connections, the connection is rejected if authentication cannot be established and returns a WSAEHOSTDOWN error.
            /// </remarks>
            public bool Authenticate
            {
                get
                {
#if WinCE
                    byte[] authbytes = m_socket.GetSocketOption(BluetoothSocketOptionLevel.RFComm, BluetoothSocketOptionName.GetAuthenticationEnabled, 4);
                    int auth = BitConverter.ToInt32(authbytes, 0);
                    return (auth == 0) ? false : true;
#else
                    object auth = m_socket.GetSocketOption(BluetoothSocketOptionLevel.RFComm, BluetoothSocketOptionName.XPAuthenticate);
                    return authenticate;
#endif
                }
                set
                {
#if WinCE
                    m_socket.SetSocketOption(BluetoothSocketOptionLevel.RFComm, BluetoothSocketOptionName.SetAuthenticationEnabled, (int)(value ? 1 : 0));
#else
                    m_socket.SetSocketOption(BluetoothSocketOptionLevel.RFComm, BluetoothSocketOptionName.XPAuthenticate, value);
                    authenticate = value;
#endif
                }
            }
            #endregion

            #region Encrypt
            /// <summary>
            /// On unconnected sockets, enforces encryption to establish a connection.
            /// Encryption is only available for authenticated connections.
            /// For incoming connections, a connection for which encryption cannot be established is automatically rejected and returns WSAEHOSTDOWN as the error.
            /// For outgoing connections, the connect function fails with WSAEACCES if encryption cannot be established.
            /// In response, the application may prompt the user to authenticate the two Bluetooth devices before connection.
            /// </summary>
            public bool Encrypt
            {
                get { return encrypt; }
                set
                {
                    m_socket.SetSocketOption(BluetoothSocketOptionLevel.RFComm, BluetoothSocketOptionName.Encrypt, (int)(value ? 1 : 0));
                    encrypt = value;
                }
            }
            #endregion

            #region Set Pin
            public void SetPin(BluetoothAddress device, string pin)
            {
#if WinXP
                if (pin != null) {
                    m_authenticator = new BluetoothWin32Authentication(device, pin);
                } else {
                    if (m_authenticator != null) {
                        m_authenticator.Dispose();
                    }
                }
#else
                byte[] link = new byte[32];

                //copy remote device address
                if (device != null)
                {
                    Buffer.BlockCopy(device.ToByteArray(), 0, link, 8, 6);
                }

                //copy PIN
                if (pin != null & pin.Length > 0)
                {
                    if (pin.Length > 16)
                    {
                        throw new ArgumentOutOfRangeException("PIN must be between 1 and 16 ASCII characters");
                    }
                    //copy pin bytes
                    byte[] pinbytes = System.Text.Encoding.ASCII.GetBytes(pin);
                    Buffer.BlockCopy(pinbytes, 0, link, 16, pin.Length);
                    BitConverter.GetBytes(pin.Length).CopyTo(link, 0);
                }

                m_socket.SetSocketOption(BluetoothSocketOptionLevel.RFComm, BluetoothSocketOptionName.SetPin, link);
#endif
            }
            #endregion

            #region Enter Sniff Mode



            public int EnterSniffMode()
            {

                byte[] policy = m_socket.GetSocketOption(BluetoothSocketOptionLevel.RFComm, BluetoothSocketOptionName.EnterSniffMode, 4);
                return (int)BitConverter.ToInt32(policy, 0);

            }
            #endregion Enter Sniff Mode

            #region Enter Sniff Mode
            public int ExitSniffMode()
            {

                byte[] policy = m_socket.GetSocketOption(BluetoothSocketOptionLevel.RFComm, BluetoothSocketOptionName.ExitSniffMode, 4);
                return (int)BitConverter.ToInt32(policy, 0);

            }
            #endregion Exit Sniff Mode
        }//class--SocketOptionHelper

    }//class--BluetoothClient

}
