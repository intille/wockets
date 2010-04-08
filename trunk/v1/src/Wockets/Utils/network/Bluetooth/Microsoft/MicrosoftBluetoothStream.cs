using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Utils.network.Bluetooth;
using Wockets;
using System.Net.Sockets;
using System.Threading;
using System.Runtime.InteropServices;

namespace Wockets.Utils.network.Bluetooth.Microsoft
{


    public class MicrosoftBluetoothStream : BluetoothStream, IDisposable
    {

        public Socket socket;
        public NetworkStream nstream;
        public MicrosoftBluetoothEndPoint _RemoteEP;
        private bool disposed = false;

        public MicrosoftBluetoothStream(CircularBuffer buffer, CircularBuffer sbuffer, byte[] address, string pin)
            : base(buffer, sbuffer, address, pin)
        {

            try
            {
                _RemoteEP = new MicrosoftBluetoothEndPoint(this.address, BluetoothStream._SerialPort);
            }
            catch (Exception e)
            {
                this.errorMessage = "MicrosoftBluetoothStream failed at the constructor";
                this.status = BluetoothStatus.Error;
            }
        }


        ~MicrosoftBluetoothStream()
        {
            Dispose();
        }


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
       /* [DllImport("btdrt.dll", SetLastError = true)]
        public static extern int BthReadRSSI(byte[] pbt, out ushort pbRSSI);
        */

        public static BluetoothStream Open(CircularBuffer buffer, CircularBuffer sbuffer, byte[] address, string pin)
        {
            //os shuts it down so make sure it is open
            try
            {
                NetworkStacks._BluetoothStack.Initialize();
            }
            catch
            {
                return null;
            }
            MicrosoftBluetoothStream btStream = new MicrosoftBluetoothStream(buffer, sbuffer, address, pin);
            btStream._Status = BluetoothStatus.Reconnecting;
            try
            {

                lock (mylock)
                {

                    btStream.socket = new Socket(BluetoothStream._AddressFamily, SocketType.Stream, BluetoothStream._ProtocolType);
                    btStream.socket.Blocking = true;

                    btStream.socket.Connect(btStream._RemoteEP);
                    btStream.nstream = new NetworkStream(btStream.socket, true);

                }


                btStream.processingThread = new Thread(new ThreadStart(btStream.Process));
                btStream.processingThread.Priority = ThreadPriority.AboveNormal;
                btStream.processingThread.Start();
                Logger.Debug("Microsoft Open:Reconnection for receiver " + btStream.hexAddress + " success spawned process thread ");

            }
            catch (Exception e)
            {
                Logger.Debug("Microsoft Open:Reconnection for receiver " + btStream.hexAddress + " failed." + e.ToString());
                btStream = null;
            }
            return btStream;
        }




        //this is the buffer used to read asynchonously from the socket. When
        //the asynchronous read returns, this is copied into the localBuffer.   
        private const int LOCAL_BUFFER_SIZE = 2048;
        private int logCounter = 0;
        private int totalBytes = 0;
        private int sentBytes = 0;
        private static object socketLock = new object();
        /*private ushort rssi;
        private int rssi_count = 0;
        private int rssi_sum = 0;*/

        //BthReadRSSI(btStream._RemoteEP.Address, out rssi);

        public override void Process()
        {
            byte[] sendByte = new byte[1];
            this.status = BluetoothStatus.Connected;
            byte[] singleReadBuffer = new byte[LOCAL_BUFFER_SIZE];
            double timestamp = 0.0;
            logCounter = 0;
            Logger.Debug("Microsoft Process:Processing thread started for receiver " + this._HexAddress + " status:" + this.status.ToString());
            while (this.status == BluetoothStatus.Connected)
            {
                int bytesReceived = 0;
                logCounter++;
                try
                {
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
                                    this.errorMessage = "MicrosoftBluetoothStream failed at Process(). Cannot send bytes to " + _RemoteEP.ToString();
                                    Logger.Debug("Receiver " + this._HexAddress + " disconnected send, tail=" + this.buffer._Tail + "," + this.buffer._Head);
                                    this.status = BluetoothStatus.Disconnected;

                                    return;
                                }


                            }

                           /* BthReadRSSI(address, out rssi);
                            if (rssi > rssi_sum)
                                rssi_sum = rssi;
                            rssi_count++;
                            if (rssi_count > 10)
                            {
                                rssi_sum = 0;
                                rssi_count = 0;
                            }*/

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

                    //socket.co
                    lock (socketLock)
                    {
                        if (socket.Available > 0)
                        {

                            bytesReceived = socket.Receive(singleReadBuffer, LOCAL_BUFFER_SIZE, SocketFlags.None);

                            totalBytes += bytesReceived;
                            // timestamp = WocketsTimer.GetUnixTime();


                            /*if (totalBytes >= 12000)
                            {
                                totalBytes = 0;
                            }*/
                        }
                    }
                    Thread.Sleep(30);
                    if (logCounter > 500)
                    {
                        Logger.Debug("Receiver " + this._HexAddress + ",sent:" + sentBytes + ",received:" + totalBytes);
                        logCounter = 0;
                    }

                    if (bytesReceived > 0)
                        disconnectionCounter = 0;
                    else
                    {
                        disconnectionCounter++;
                        if (disconnectionCounter > MAX_DISCONNECTION_COUNTER)
                        {
                            Logger.Debug("Receiver " + this._HexAddress + " disconnected timeout, tail=" + this.buffer._Tail + ",head=" + this.buffer._Head);
                            this.status = BluetoothStatus.Disconnected;
                            return;
                        }
                    }



                }
                catch (Exception e)
                {
                    Logger.Debug("Receiver " + this._HexAddress + " disconnected other exception, tail=" + this.buffer._Tail + "," + this.buffer._Head);
                    this.status = BluetoothStatus.Disconnected;
                    return;
                }




                int ii;
                int mytail = this.buffer._Tail;
                for (ii = 0; ii < bytesReceived; ii++)
                {
                    // this.buffer._Timestamp[this.buffer._Tail] = timestamp;
                    this.buffer._Bytes[mytail++] = singleReadBuffer[ii];
                    mytail %= this.buffer._Bytes.Length;
                }
                this.buffer._Tail = mytail;
            }

        }
    }
}
