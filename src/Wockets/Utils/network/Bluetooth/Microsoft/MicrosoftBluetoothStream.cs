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
    public class MicrosoftBluetoothStream:BluetoothStream
    {

        private BluetoothClient client;
        private Socket socket;
        private NetworkStream nstream;
        private BluetoothAddress btAddress;
        private static int timeout = 3000;
        private static int timeoutMultiplier = 1;
        private static int connectionFailures = 0;

        public MicrosoftBluetoothStream(byte[] buffer, byte[] address, string pin): base(buffer,address,pin)
        {
            try
            {   
                btAddress = new BluetoothAddress(this.address);
                if (this.pin != null)                                   
                    BluetoothSecurity.SetPin(btAddress, this.pin);
                
            }
            catch (Exception e)
            {
                this.errorMessage = "MicrosoftBluetoothStream failed at the constructor";
                this.status = BluetoothStatus.Error;                
            }
        }

        public override bool Open()
        {
            try
            {   

                    
                client = new BluetoothClient();                
                if (processingThread != null)
                    processingThread.Abort();
                client.Connect(btAddress, BluetoothService.SerialPort);
    
                socket = client.Client;               
                socket.Blocking = true;
                nstream = client.GetStream();

                //start the processing thread
                this.status = BluetoothStatus.Connected;      
                processingThread = new Thread(new ThreadStart(Process));
                processingThread.Start();
                
            }
            catch (Exception e)
            {
                
                this.errorMessage = "MicrosoftBluetoothStream failed at opening a connection to " + btAddress.ToString();
                this.status = BluetoothStatus.Disconnected;
                Thread.Sleep(500);
                connectionFailures++;
                if (connectionFailures == 3)
                {
                    if (timeoutMultiplier <= 3)
                        timeoutMultiplier++;
                    connectionFailures=0;
                }
                return false;
            }
            return true;
        }
        public override void Process()
        {

            while (this.status == BluetoothStatus.Connected)
            {
                int bytesReceived = 0;

                try
                {

                    lock (this.toSend)
                    {
                        if (this.toSend.Count != 0)
                        {
                            foreach (byte[] msg in this.toSend)
                            {
                                for (int k = 0; (k < msg.Length); k++)
                                {

                                    if (socket.Send(msg, k, 1, SocketFlags.None) != 1)
                                    {
                                        this.errorMessage = "MicrosoftBluetoothStream failed at Process(). Cannot send bytes to " + btAddress.ToString();
                                        this.status = BluetoothStatus.Disconnected;
                                        return;
                                    }


                                    Thread.Sleep(20);
                                }

                            }
                            this.toSend.Clear();
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
                        if (availableBytes > 0)
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
                            this.status = BluetoothStatus.Disconnected;
                            return;
                        }

                    }

                }             
                catch (Exception e)
                {
                    this.errorMessage = "MicrosoftBluetoothStream failed at Process(). " + e.Message + " to " + btAddress.ToString();
                    this.status = BluetoothStatus.Disconnected;
                    return;
                }

            }

        }
        public override bool Close()
        {
            if (this.status!=BluetoothStatus.Disconnected)
                this.status = BluetoothStatus.Disconnected;
            processingThread.Join();
            if (processingThread != null)
                processingThread.Abort();

            try
            {
                client.Close();
                socket.Close();
                nstream.Close();
            }
            catch (Exception)
            {
            }

            processingThread = null;
            nstream = null;
            socket = null;
            client = null; 
            //GC.Collect();
            //GC.WaitForPendingFinalizers();
            //Thread.Sleep(10000);
           
            return true;
        }
    }
}
