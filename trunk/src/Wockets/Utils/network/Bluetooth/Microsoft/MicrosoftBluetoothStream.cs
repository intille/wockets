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
        public Thread readingThread;
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
        
        /*~MicrosoftBluetoothStream()
        {
            //Dispose(true);
        }*/

          
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

            readingThread.Join();

      


                nstream.Close();
                socket.Close();
                client.Close();

                //ms_stream = null;
                socket = null;
                client = null;
                nstream = null;

                //BluetoothRadio.PrimaryRadio.Mode = RadioMode.Connectable;

            

        }
        public static MicrosoftBluetoothStream OpenStatic(byte[] buffer, CircularBuffer sbuffer, byte[] address, string pin)
        {
            MicrosoftBluetoothStream newStream = new MicrosoftBluetoothStream(buffer, null, address, pin);

            try
            {

                lock (mylock)
                {
                    newStream.client = new BluetoothClient(); 
                    BluetoothRadio.PrimaryRadio.Mode = RadioMode.Connectable;
                    //BluetoothAddress bt_addr = new BluetoothAddress(address);
                    if (pin != null)
                        BluetoothSecurity.SetPin(newStream.btAddress, pin);


                    newStream.client.Connect(newStream.btAddress, BluetoothService.SerialPort);
                    newStream.socket = newStream.client.Client;
                    newStream.socket.Blocking = true;
                    newStream.nstream = newStream.client.GetStream();

                }

               
                newStream.readingThread = new Thread(new ThreadStart(newStream.readingFunction));
                newStream.readingThread.Priority = ThreadPriority.Highest;
                newStream.readingThread.Start();               
                newStream._Status = BluetoothStatus.Connected;

            }
            catch (Exception e)
            {
                newStream.disposed = true;
                throw;
            }
            return newStream;
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


        private byte[] localBuffer;
        //this is the buffer used to read asynchonously from the socket. When
        //the asynchronous read returns, this is copied into the localBuffer.
        private byte[] singleReadBuffer;
        private static int iii = 0;
        NetworkStream n;
        private const int DEFAULT_BUFFER_SIZE = 8000;
        private int head = 0;
        //private int tail = 0;
        private void readingFunction()
        {
            double prevTime = 0;
            double currentTime = 0;
            byte[] buffer = new byte[100];

            double nodataTimer = WocketsTimer.GetUnixTime();
            int sendTimer = 0;
            byte[] sendByte = new byte[1];
            sendByte[0] = 0xbb;

            n = client.GetStream();
            this.buffer = new byte[DEFAULT_BUFFER_SIZE];
            this.status = BluetoothStatus.Connected;
            singleReadBuffer = new byte[DEFAULT_BUFFER_SIZE];

            //TextWriter tttw = new StreamWriter("samples"+(iii++)+".csv");





            while (!disposed)
            {

                //if (!comPort.IsOpen)
                //  return;
                if (!client.Connected)
                    return;

                int bytesReceived = 0;
                bool readHappened = false;
                int currentBytes = tail - head;
                if (currentBytes < 0)
                    currentBytes = DEFAULT_BUFFER_SIZE + currentBytes;



                try
                {

                    readHappened = true;

                    try
                    {

                        /*byte[] cmd = new byte[50];
                        for (int i = 0; (i < 50); i++)
                            cmd[i] = (byte)36;
                        //SW,0640 1 sec
                        btSocket.Send(cmd, 3, SocketFlags.None);
                        Thread.Sleep(100);
                        cmd[0] = (byte)'S';
                        cmd[1] = (byte)'I';
                        cmd[2] = (byte)',';
                        cmd[3] = (byte)'0';
                        cmd[4] = (byte)'2';
                        cmd[5] = (byte)'0';
                        cmd[6] = (byte)'0';
                        cmd[7] = (byte)13;
                        btSocket.Send(cmd, 8, SocketFlags.None); ;
                        Thread.Sleep(100);
                         */

                        if (sendTimer > 2000)
                        {

                            socket.Send(sendByte, 1, SocketFlags.None); ;
                            sendTimer = 0;

                        }
                        sendTimer++;

                        if (socket.Available > 0)
                        {
                            currentTime = WocketsTimer.GetUnixTime();
                            bytesReceived = socket.Receive(singleReadBuffer, (DEFAULT_BUFFER_SIZE - currentBytes > singleReadBuffer.Length) ? singleReadBuffer.Length : DEFAULT_BUFFER_SIZE - currentBytes, SocketFlags.None);
                            //batchTimestamps.Add(currentTime);
                            // batchBytes.Add(bytesReceived);
                        }

                        Thread.Sleep(10);


                        if (bytesReceived > 0)
                        {
                            nodataTimer = currentTime;
                            disconnectionCounter = 0;
                            // tttw.WriteLine(currentTime+","+bytesReceived);
                            //tttw.Flush();
                        }
                        else
                        {
                            disconnectionCounter++;
                            //if ((currentTime - nodataTimer) > 1000)
                            if (disconnectionCounter > MAX_DISCONNECTION_COUNTER)
                            {
                                //socketDead = true;
                                this._Status = BluetoothStatus.Disconnected;

                                return;
                            }
                        }
                        /*
                            if (sendTimer == 0)
                                sendTimer = currentTime;

                            if ((currentTime-sendTimer) >= 1000)
                            {
                                btSocket.Send(xxx);
                                if (xxx[0] == 255)
                                    xxx[0] = 0;
                                xxx[0] = (byte)(xxx[0] + 1);
                                sendTimer = 0;
                            }

                            */
                        prevTime = currentTime;


                    }
                    catch (Exception e)
                    {
                       // socketDead = true;
                        this._Status = BluetoothStatus.Disconnected;
                    }


                }
                catch (Exception e)
                {
                    throw e;
                }

                //this is a timeout. If we get too many of them, we classify that
                //as a socket that has been disconnected

                /*if (readHappened && bytesReceived == 0)
                {
                    List<DateTime> newTimeouts = timeoutTimestamps.FindAll(oldEnoughPredicate);
                    newTimeouts.Add(DateTime.Now);
                    if (newTimeouts.Count > MAX_TIMEOUTS)
                    {
                        socketDead = true;
                    }
                    timeoutTimestamps = newTimeouts;
                }*/



                int ii;
                for (ii = 0; ii < bytesReceived && ii < (DEFAULT_BUFFER_SIZE - currentBytes); ii++)
                {
                    this.buffer[tail++] = singleReadBuffer[ii];
                    tail %= DEFAULT_BUFFER_SIZE;
                }

               // tail = tail % this.buffer.Length;

            }

            //tttw.Close();

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
                            Logger.Warn(" D "+btAddress.ToString());
                            this.status = BluetoothStatus.Disconnected;
                            return;
                        }

                    }


                }
                catch (Exception e)
                {
                    this.errorMessage = "MicrosoftBluetoothStream failed at Process(). " + e.Message + " to " + btAddress.ToString();
                    Logger.Warn(" D "+btAddress.ToString());
                   // Dispose();
                    this.status = BluetoothStatus.Disconnected;                   
                    return;
                }

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
