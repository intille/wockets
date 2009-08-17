using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Utils.network.Bluetooth;
using InTheHand.Net;
using InTheHand.Net.Bluetooth;
using InTheHand.Net.Sockets;
using System.Net.Sockets;
using System.Threading;

namespace Wockets.Utils.network.Bluetooth.Microsoft
{
    public class MicrosoftBluetoothStream : BluetoothStream
    {

        private BluetoothClient client=null;
        private Socket socket;
        private NetworkStream nstream;
        private BluetoothAddress btAddress;
        //private static int x = 0;
        //private static object mylock= new object();
        private bool disposed = false;


        public MicrosoftBluetoothStream(byte[] buffer, CircularBuffer sbuffer, byte[] address, string pin)
            : base(buffer,sbuffer, address, pin)
        {

            try
            {
                btAddress = new BluetoothAddress(this.address);

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
        
        public override bool Open()
        {

            try
            {

                //if (client==null)



                lock (mylock)
                {
                    client = new BluetoothClient();
                    //BluetoothRadio.PrimaryRadio.Mode = RadioMode.Connectable;
                    //BluetoothSecurity.SetPin(btAddress, "1234");


                    client.Connect(btAddress, BluetoothService.SerialPort);
                    //client.Connect(btAddress, BluetoothService.SerialPort, 10);
                    //client.Connect(btAddress, BluetoothService.SerialPort, 3000);
                    socket = client.Client;
                    socket.Blocking = true;
                    nstream = client.GetStream();

                }

                //start the processing thread
                this.status = BluetoothStatus.Connected;
                processingThread = new Thread(new ThreadStart(Process));
                processingThread.Priority = ThreadPriority.Highest;
                processingThread.Start();


            }
            catch (Exception e)
            {

                this.errorMessage = "MicrosoftBluetoothStream failed at opening a connection to " + btAddress.ToString();
                this.status = BluetoothStatus.Disconnected;
                return false;
            }
            return true;
        }
        public override void Process()
        {
            int sendTimer = 0;
            byte[] sendByte = new byte[1];
            sendByte[0] = 0xbb;


            while (this.status == BluetoothStatus.Connected)
            {
                int bytesReceived = 0;

                try
                {

                   /* if (sendTimer > 200)
                    {

                        if (socket.Send(sendByte, 1, SocketFlags.None) <= 0)
                        {
                            this.errorMessage = "MicrosoftBluetoothStream failed at Process(). Cannot send bytes to " + btAddress.ToString();
                            this.status = BluetoothStatus.Disconnected;
                        }
                        sendTimer = 0;
                        Thread.Sleep(50);
                    }
                    sendTimer++;
                    */
                    lock (this.sbuffer)
                    {
                        int counter = 0;
                        while (this.sbuffer._Tail != this.sbuffer._Head)
                        {
                            if (socket.Send(this.sbuffer._Bytes, this.sbuffer._Head, 1, SocketFlags.None) != 1)
                            {
                                this.errorMessage = "MicrosoftBluetoothStream failed at Process(). Cannot send bytes to " + btAddress.ToString();
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


           
                    int availableBytes = socket.Available;
                    if (availableBytes > 0)
                    {
                        bytesReceived = 0;
                        //if we will pass the end of buffer receive till the end then receive the rest
                        if ((tail + availableBytes) > this.buffer.Length)
                        {
                            bytesReceived = socket.Receive(this.buffer, tail, this.buffer.Length - tail, SocketFlags.None);
                            availableBytes -= bytesReceived;
                            tail = (tail + bytesReceived) % this.buffer.Length;
                        }
                        bytesReceived += socket.Receive(this.buffer, tail, availableBytes, SocketFlags.None);
                        tail = (tail + bytesReceived) % this.buffer.Length;
                    }

                    Thread.Sleep(30);

                    if (bytesReceived > 0)
                        disconnectionCounter = 0;
                    else
                    {
                        disconnectionCounter++;
                        if (disconnectionCounter > MAX_DISCONNECTION_COUNTER)
                        {
                            this.errorMessage = "MicrosoftBluetoothStream failed at Process(). Disconnection timeout to " + this._HexAddress;
                 //           Dispose();
                            this.status = BluetoothStatus.Disconnected;
                            return;
                        }

                    }


                }
                catch (Exception e)
                {
                    this.errorMessage = "MicrosoftBluetoothStream failed at Process(). " + e.Message + " to " + btAddress.ToString();
                   // Dispose();
                    this.status = BluetoothStatus.Disconnected;                   
                    return;
                }

            }

        }

        protected override void Dispose(bool disposing)
        {
           
            lock (mylock)
            {
                
                if ((!disposed)&&(disposing))
                {
                    // Release managed resources.
                    try
                    {
                        
                        nstream.Close();
                    }
                    catch (Exception)
                    {
                    }
                    try
                    {
                        socket.Close();                     
                    }
                    catch (Exception)
                    {
                    }


                    try
                    {
                        client.Close();
                    }
                    catch (Exception e)
                    {
                    }

                    //processingThread = null;
                    nstream = null;
                    socket = null;
                    client = null;

                    // Release unmanaged resources.
                    // Set large fields to null.
                    // Call Dispose on your base class.
                    base.Dispose(disposing);
                    this.status = BluetoothStatus.Disposed;
                    disposed = true;
                }
                
            }
        }


/*
        public void Dispose()//bool Close()
        {
            lock (this)
            {
                if (disposed)
                    return;
                disposed = true;
            }



            processingThread.Join();


            try
            {
                nstream.Close();
            }
            catch (Exception)
            {
            }
            try
            {
                socket.Close();
            }
            catch (Exception)
            {
            }


            try
            {
                client.Close();
            }
            catch (Exception e)
            {
            }

            processingThread = null;
            nstream = null;
            socket = null;
            client = null;
            this.status = BluetoothStatus.Disconnected;


            //return true;
        }
 */
    }
}
