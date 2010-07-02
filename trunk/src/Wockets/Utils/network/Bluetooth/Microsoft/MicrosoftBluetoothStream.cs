using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Utils.network.Bluetooth;
using Wockets;
using Wockets.Data.Configuration;
using Wockets.Exceptions;
using System.Net.Sockets;
using System.Threading;


#if (!PocketPC)
using InTheHand.Net;
using InTheHand.Net.Sockets;
using InTheHand.Net.Bluetooth;
#endif

namespace Wockets.Utils.network.Bluetooth.Microsoft
{


    public class MicrosoftBluetoothStream : BluetoothStream,IDisposable
    {

        // Socket Definitions
        /// <summary>
        /// The bluetooth communication socket
        /// </summary>
        public Socket socket;

        /// <summary>
        /// The network stream attached to the socket
        /// </summary>
        public NetworkStream nstream;        

        /// <summary>
        /// The remote endpoint address of the remote bluetooth device
        /// </summary>
#if (PocketPC)
        public MicrosoftBluetoothEndPoint _RemoteEP;
#else
        public BluetoothEndPoint _RemoteEP;
#endif

        /// <summary>
        /// Specifies if the object has been disposed
        /// </summary>
        private bool disposed = false;

        /// <summary>
        /// Receive buffer size
        /// </summary>
        private const int LOCAL_BUFFER_SIZE = 2048;

        /// <summary>
        /// Total bytes read 
        /// </summary>
        private int totalBytes = 0;

        /// <summary>
        /// Number of bytes sent
        /// </summary>
        private int sentBytes = 0;

        /// <summary>
        /// A class bound lock to synchronize connections
        /// </summary>
        private static object socketLock = new object();

       

        /// <summary>
        /// The constructor sets up a Bluetooth stream object with refrences to the send and receive buffers
        /// </summary>
        /// <param name="buffer">Handle to a circular receive buffer</param>
        /// <param name="sbuffer">Handle to a circular send buffer</param>
        /// <param name="address">A machine independent (Little or Big Endian) byte array of the bluetooth address </param>
        /// <param name="pin">A pin for the remote bluetooth device</param>
        public MicrosoftBluetoothStream(CircularBuffer buffer, CircularBuffer sbuffer, byte[] address, string pin)
            : base(buffer,sbuffer, address, pin)
        {

            try
            {
#if (PocketPC)
                _RemoteEP = new MicrosoftBluetoothEndPoint(this.address, BluetoothStream._SerialPort);
#else
                BluetoothAddress btaddress = new BluetoothAddress(this.address);
                //Set BT Device Address
                
                //Set BT Device Pin
                //BluetoothSecurity.SetPin((BluetoothAddress)btaddress, "1234");

                // Create a connection channel specifying the Bluetooth-Serial end-points 
                _RemoteEP = new BluetoothEndPoint((BluetoothAddress)btaddress, BluetoothService.SerialPort);
#endif

            }
            catch (Exception e)
            {
                CurrentWockets._LastError = ErrorCodes.REMOTE_ENDPOINT_CREATION_FAILED;
                CurrentWockets._LastErrorMessage = "Failed to setup connection endpoint for " + this._HexAddress + ". " + e.ToString();
                if (CurrentWockets._Configuration._SoftwareMode == SoftwareConfiguration.DEBUG)
                    Logger.Debug("MicrosoftBluetoothStream: Constructor: <" + ErrorCodes.REMOTE_ENDPOINT_CREATION_FAILED + ">: Failed to setup connection endpoint for " + this._HexAddress + ". " + e.ToString());
                throw new Exception("MicrosoftBluetoothStream: Constructor: <" + ErrorCodes.REMOTE_ENDPOINT_CREATION_FAILED + ">: Failed to setup connection endpoint for " + this._HexAddress + ". " + e.ToString());
            }
        }
        
        
        /// <summary>
        /// A bluetooth stream destructor that allows the is invoked by the garbage collecter, this is necessary and provides
        /// more stable connections
        /// </summary>
        ~MicrosoftBluetoothStream()
        {
           Dispose();
        }

        /// <summary>
        /// Dispose and deallocates any resources with the Bluetooth stream
        /// </summary>
        public void Dispose()
        {
            lock (this)
            {
                if (disposed)
                    return;
                disposed = true;
            }

            try
            {
                IDisposable idStream = nstream;
                if (idStream != null)
                {
                    //dispose the stream which will also close the socket
                    idStream.Dispose();
                }
            }
            catch (Exception)
            {
            }

        }
        

        /// <summary>
        /// A static method that opens a connection to a Bluetooth serial service and spawns a processing thread
        /// </summary>
        /// <param name="buffer">Handle to a circular receive buffer</param>
        /// <param name="sbuffer">Handle to a circular send buffer</param>
        /// <param name="address">A machine independent (Little or Big Endian) byte array of the bluetooth address</param>
        /// <param name="pin">A pin for the remote bluetooth device</param>
        /// <returns>A BluetoothStream object on success, otherwise a null</returns>
        public static BluetoothStream Open(CircularBuffer buffer,CircularBuffer sbuffer, byte[] address, string pin)
        {
            //Initialize the Bluetooth stack
            if (!NetworkStacks._BluetoothStack.Initialize())
                return null;
           
            try
            {
                // Initialize the microsoft bluetooth stream
                MicrosoftBluetoothStream btStream = new MicrosoftBluetoothStream(buffer, sbuffer, address, pin);
                btStream._Status = BluetoothStatus.Reconnecting;
                   
                // Critical section: Allow one connection at a time
                lock (mylock)
                {                    
                    btStream.socket = new Socket(BluetoothStream._AddressFamily, SocketType.Stream, BluetoothStream._ProtocolType);
                    btStream.socket.Blocking = true;
                    btStream._ConnectionTime = WocketsTimer.GetUnixTime(DateTime.Now);
                    btStream.socket.Connect(btStream._RemoteEP);       
                    btStream._CurrentConnectionUnixTime = WocketsTimer.GetUnixTime(DateTime.Now);
                    btStream._ConnectionTime = btStream._CurrentConnectionUnixTime - btStream._ConnectionTime;
                    btStream.nstream = new NetworkStream(btStream.socket, true);
                }


                // Spawn the processing thread
                btStream.processingThread = new Thread(new ThreadStart(btStream.Process));
                btStream.processingThread.Priority = ThreadPriority.AboveNormal;
                btStream.processingThread.Start();                
                if (CurrentWockets._Configuration._SoftwareMode == SoftwareConfiguration.DEBUG)
                    Logger.Debug("MicrosoftBluetoothStream: Open: Successful connection to" + btStream._HexAddress + ".");
                return btStream;
            }
            catch (Exception e)
            {
                // Exception failed to connect
                CurrentWockets._LastError = ErrorCodes.CONNECTION_FAILED_TO_OPEN;
                string hex = "";
                for (int i = 0; i < address.Length; i++)
                    hex += address[i].ToString("X2");          
                CurrentWockets._LastErrorMessage = "Failed to open bluetooth connection to " + hex + ". " + e.ToString();
                Logger.Error("MicrosoftBluetoothStream: Open: <" + ErrorCodes.CONNECTION_FAILED_TO_OPEN + ">: Failed to open connection to " +hex + ". " + e.ToString());
                return null;
            }
            
        }


   
        /// <summary>
        /// The method for the processing thread that handles receiving and transmitting data
        /// </summary>
        public override void Process()
        {
            byte[] sendByte = new byte[1];
            this._Status = BluetoothStatus.Connected;
            byte[] singleReadBuffer = new byte[LOCAL_BUFFER_SIZE];

            
            if (CurrentWockets._Configuration._SoftwareMode == SoftwareConfiguration.DEBUG)
                Logger.Debug("MicrosoftBluetoothStream: Process: Processing thread started for connection " + this._HexAddress);

            while (this._Status == BluetoothStatus.Connected)
            {            
                int bytesReceived = 0;

                try
                {

                    // Transmit data if needed 1 byte at a time, for a maximum of 10 bytes in each iteration
                    // then receive to avoid substantial delays
                    lock (this.sbuffer)
                    {
                        int counter = 0;
                        while (this.sbuffer._Tail != this.sbuffer._Head)
                        {
                            sendByte[0] = this.sbuffer._Bytes[this.sbuffer._Head];
                            lock (socketLock)
                            {
                                if (socket.Send(sendByte, 1, SocketFlags.None) != 1)
                                {                                    
                                    CurrentWockets._LastError = ErrorCodes.SOCKET_SEND_FAILED;
                                    CurrentWockets._LastErrorMessage = "Failed to send data to " + this._HexAddress;                       
                                    Logger.Error("MicrosoftBluetoothStream: Process: <" + ErrorCodes.SOCKET_SEND_FAILED + ">: Failed to send data to " + this._HexAddress);
                                    this._Status = BluetoothStatus.Disconnected;
                                    return;
                                }
                            }
                            sentBytes++;

                            if (this.sbuffer._Head >= (this.sbuffer._Bytes.Length - 1))
                                this.sbuffer._Head = 0;
                            else
                                this.sbuffer._Head++;

                            Thread.Sleep(20);
                            counter++;
                            if (counter == 10)
                                break;
                        }
                    }

       
                    // Receive data
                    lock (socketLock)
                    {
                        if (socket.Available > 0)
                        {

                            bytesReceived = socket.Receive(singleReadBuffer, LOCAL_BUFFER_SIZE, SocketFlags.None);
                            totalBytes += bytesReceived;
                        }
                    }

                    // Sleep for a specific length of time, defaults to 30 milliseconds
                    Thread.Sleep(this.pollingInterval);
                  

                    // Timeout if data is not received within a specific time, defaults to 12 seconds
                    if (_TimeoutEnabled)
                    {
                        if (bytesReceived > 0)
                            timeoutIterationsCounter = 0;
                        else
                        {
                            timeoutIterationsCounter++;
                            if (timeoutIterationsCounter > iterationsToTimeout)
                            {
                                CurrentWockets._LastError = ErrorCodes.CONNECTION_TIMEOUT;
                                CurrentWockets._LastErrorMessage = "Connection " + this._HexAddress + " timed out.";                                
                                Logger.Error("MicrosoftBluetoothStream: Process: <" + ErrorCodes.CONNECTION_TIMEOUT + ">: Connection " + this._HexAddress + " timed out.");
                                this._Status = BluetoothStatus.Disconnected;
                                return;
                            }

                        }
                    }



                }
                catch (Exception e)
                {


                    CurrentWockets._LastError =ErrorCodes.CONNECTION_FAILED;
                    CurrentWockets._LastErrorMessage = "Connection " + this._HexAddress + " failed.";
                    Logger.Error("MicrosoftBluetoothStream: Process: <" + ErrorCodes.CONNECTION_FAILED + ">: Connection " + this._HexAddress + " failed. "+e.Message+". "+e.StackTrace +".");
                    this._Status = BluetoothStatus.Disconnected;
                    return;
                }


                // Copy received bytes to a non-local referenced buffer
                int ii;
                int mytail = this.buffer._Tail;
                for (ii = 0; ii < bytesReceived; ii++)
                {
                    this.buffer._Bytes[mytail++] = singleReadBuffer[ii];
                    mytail %= this.buffer._Bytes.Length;                                       
                }
                this.buffer._Tail =mytail;
            }

        }   
    }
}
