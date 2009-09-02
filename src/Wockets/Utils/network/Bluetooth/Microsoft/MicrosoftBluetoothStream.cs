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

        public BluetoothClient client=null;
        public Socket socket;
        public NetworkStream nstream;
        public BluetoothAddress btAddress;
        private bool disposed = false;


        public MicrosoftBluetoothStream(CircularBuffer buffer, CircularBuffer sbuffer, byte[] address, string pin)
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
                client.Close();
            }
            catch (Exception)
            {
            }

            socket = null;
            client = null;
            nstream = null;
        }
        
        public static BluetoothStream Open(CircularBuffer buffer,CircularBuffer sbuffer, byte[] address, string pin)
        {
            MicrosoftBluetoothStream btStream = new MicrosoftBluetoothStream(buffer,sbuffer, address, pin);

            try
            {

                lock (mylock)
                {
                    btStream.client = new BluetoothClient(); 
                    BluetoothRadio.PrimaryRadio.Mode = RadioMode.Connectable;

                    btStream.client.Connect(btStream.btAddress, BluetoothService.SerialPort);
                    btStream.socket = btStream.client.Client;
                    btStream.socket.Blocking = true;
                    btStream.nstream = btStream.client.GetStream();

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
        /*
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
        }*/


     
        //this is the buffer used to read asynchonously from the socket. When
        //the asynchronous read returns, this is copied into the localBuffer.   
        private const int LOCAL_BUFFER_SIZE = 2048;
        private const int DEFAULT_BUFFER_SIZE = 4096;

        //private int tail = 0;
        public override void Process()
        {

            int sendTimer = 0;
            byte[] sendByte = new byte[1];            
            
            //this.buffer = new byte[DEFAULT_BUFFER_SIZE];
            //this.sbuffer = new CircularBuffer(256);
           // this.sbuffer[0] = 0xbb;
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


/*
                    if (sendTimer > 2000)
                    {
                       
                        socket.Send(sendByte, 1, SocketFlags.None); 
                        sendTimer = 0;

                    }
                    sendTimer++;*/
                    

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

            try
            {
                client.Close();
            }
            catch (Exception)
            {
            }
        }



        /*
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
         */


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
