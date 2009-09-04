using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Utils.network.Bluetooth;
using Wockets;
using System.Net.Sockets;
using System.Threading;

namespace Wockets.Utils.network.Bluetooth.Microsoft
{


    public class MicrosoftBluetoothStream : BluetoothStream,IDisposable
    {

        public Socket socket;
        public NetworkStream nstream;        
        public MicrosoftBluetoothEndPoint _RemoteEP;
        private bool disposed = false;

        public MicrosoftBluetoothStream(CircularBuffer buffer, CircularBuffer sbuffer, byte[] address, string pin)
            : base(buffer,sbuffer, address, pin)
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
        
        public static BluetoothStream Open(CircularBuffer buffer,CircularBuffer sbuffer, byte[] address, string pin)
        {
            MicrosoftBluetoothStream btStream = new MicrosoftBluetoothStream(buffer,sbuffer, address, pin);

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
                btStream.processingThread.Priority = ThreadPriority.Highest;
                btStream.processingThread.Start();

            }
            catch (Exception e)
            {                
                btStream = null;
            }
            return btStream;
        }



     
        //this is the buffer used to read asynchonously from the socket. When
        //the asynchronous read returns, this is copied into the localBuffer.   
        private const int LOCAL_BUFFER_SIZE = 2048;

        public override void Process()
        {
            byte[] sendByte = new byte[1];                        
            this.status = BluetoothStatus.Connected;
            byte[] singleReadBuffer = new byte[LOCAL_BUFFER_SIZE];

            while (this.status== BluetoothStatus.Connected)
            {
            

                int bytesReceived = 0;


                try
                {
                    lock (this.sbuffer)
                    {
                        int counter = 0;
                        while (this.sbuffer._Tail != this.sbuffer._Head)
                        {
                            sendByte[0] = this.sbuffer._Bytes[this.sbuffer._Head];
                            if (socket.Send(sendByte, 1, SocketFlags.None) != 1)
                            {
                                this.errorMessage = "MicrosoftBluetoothStream failed at Process(). Cannot send bytes to " + _RemoteEP.ToString();
                                this.status = BluetoothStatus.Disconnected;
                                return;
                            }

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

                    if (socket.Available > 0)
                        bytesReceived = socket.Receive(singleReadBuffer, LOCAL_BUFFER_SIZE, SocketFlags.None);                    

                    Thread.Sleep(10);


                    if (bytesReceived > 0)                       
                        disconnectionCounter = 0;                    
                    else
                    {
                        disconnectionCounter++;
                        if (disconnectionCounter > MAX_DISCONNECTION_COUNTER)
                        {
                            this.status= BluetoothStatus.Disconnected;
                          
                        }
                    }



                }
                catch (Exception e)
                {
                    this.status = BluetoothStatus.Disconnected;
                }



                int ii;
                for (ii = 0; ii < bytesReceived; ii++)
                {
                    this.buffer._Bytes[this.buffer._Tail++] = singleReadBuffer[ii];
                    this.buffer._Tail %= this.buffer._Bytes.Length;
                }

            }

        }   
    }
}
