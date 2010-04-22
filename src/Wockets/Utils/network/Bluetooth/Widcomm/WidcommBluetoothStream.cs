using System;
using System.Collections.Generic;
using System.Collections;
using System.Text;
using Wockets.Utils.network.Bluetooth;
//using System.IO.Ports;
using System.Threading;
using System.Globalization;
using Microsoft.Win32;
using System.Runtime.InteropServices;
using OpenNETCF.IO.Ports;
namespace Wockets.Utils.network.Bluetooth.Widcomm
{
    public class WidcommBluetoothStream : BluetoothStream
    {
        private int comPort = 0;
        private static Hashtable spps=new Hashtable();
        private int index = 0;       
        
        private static int x = 0;
        public string _COMPORT = "";
        private static SerialPort[] spp = new SerialPort[2]{null,null};

        private static IntPtr[] wdStack = new IntPtr[2]{IntPtr.Zero,IntPtr.Zero};
        

        public WidcommBluetoothStream(CircularBuffer buffer, CircularBuffer sbuffer, byte[] address, string pin)
            : base(buffer, sbuffer, address, pin)
        {
            if (wdStack[0] != IntPtr.Zero)
                WidcommAPI.DeleteWidcommStack(wdStack[0]);
            Thread.Sleep(2000);
           wdStack[0] = WidcommAPI.CreateWidcommStack();
           if (wdStack[0] == null)
               throw new Exception("Cannot create stack");             
        }
        public bool Open()
        {
            try

            {
                lock (mylock)
                {

                    if (processingThread != null)
                        processingThread.Abort();

                    long bt_address = long.Parse(this._HexAddress, NumberStyles.HexNumber, CultureInfo.CurrentCulture.NumberFormat);
                    //Thread.Sleep(10000);
                    int r = WidcommAPI.SppRemoveConnection(wdStack[0]);
                    Thread.Sleep(3000);
                    r=WidcommAPI.SppCreateConnection(wdStack[0], (byte)1, bt_address);
                    Thread.Sleep(3000);
                    if (r != 1)
                    {
                        WidcommAPI.SppRemoveConnection(wdStack[0]);
                        NetworkStacks._BluetoothStack = null;

                    }
 
                            /* RegistryKey rk = Registry.LocalMachine.OpenSubKey("Software\\WIDCOMM\\BTConfig\\AutoConnect");
                             string[] subkeys = rk.GetSubKeyNames();
                             if (subkeys.Length > 0)
                             {
                                 for (int i = 0; (i < subkeys.Length); i++)
                                 {
                                     int com = Convert.ToInt32(subkeys[i]);
                                     //if (WidcommBluetoothStack._PortUsed[com])
                                       //  continue;
                                     if (com == 11)
                                     {
                                         _COMPORT = "BTC1";
                                         WidcommBluetoothStack._PortUsed[com] = true;
                                     }
                                     else if (com == 12)
                                     {
                                         _COMPORT = "BTC2";
                                         WidcommBluetoothStack._PortUsed[com] = true;
                                     }
                                     else if (com == 13)
                                     {
                                         _COMPORT = "BTC3";
                                         WidcommBluetoothStack._PortUsed[com] = true;
                                     }

                                     break;


                                 }

                                 if (_COMPORT.Length > 2)
                                     break;
                             }*/


                    int com = WidcommAPI.SppComPort(wdStack[0]);
                    //if (com == 11)
                    //  _COMPORT = "BTC1";
                    //else if (com == 12)
                    //  _COMPORT = "BTC2";
                    //else if (com == 13)
                    _COMPORT = "BTC3";
        
                    if ((_COMPORT.Length > 2) && ((r == 1)|| (r==3)))
                    {
                 
                      
              
                        spp[0] = new OpenNETCF.IO.Ports.SerialPort(_COMPORT + ":", 38400, OpenNETCF.IO.Ports.Parity.None, 8, OpenNETCF.IO.Ports.StopBits.One);//new SerialPort(_COMPORT, 38400, Parity.None, 8, StopBits.One);                    
                        if (!spp[0].IsOpen)
                            spp[0].Open();
                        //spps.Add(this._HexAddress, spp);


                        this._Status = BluetoothStatus.Connected;
                        //start the processing thread
                        processingThread = new Thread(new ThreadStart(Process));
                        processingThread.Start();
                    }
             
                }
            }
            catch (Exception e)
            {
                spp[0].Close();
                spp[0].Dispose();
                NetworkStacks._BluetoothStack = null;
                
                CurrentWockets._LastError = Wockets.Exceptions.ErrorCodes.CONNECTION_FAILED_TO_OPEN;
                CurrentWockets._LastErrorMessage = "MicrosoftBluetoothStream failed at Open() " + this._HexAddress;
                this._Status = BluetoothStatus.Disconnected;
                return false;
            }
            return true;
        }

        private const int LOCAL_BUFFER_SIZE = 2048;
        private int[] storage = new int[10];
        int storageIndex = 0;
        int lowest_com = 0;
        public override void Process()
        {
            int sendTimer = 0;
            byte[] sendByte = new byte[1];
            sendByte[0] = 0xbb;
            byte[] singleReadBuffer = new byte[LOCAL_BUFFER_SIZE];

            while (this._Status == BluetoothStatus.Connected)
            {
                int bytesReceived = 0;

                try
                {

                    if (sendTimer > 100)
                    {
                        spp[0].Write(sendByte, 0, 1);
                        //WidcommAPI.SendData(wdStack, sendByte, 1);
                        sendTimer = 0;
                        Thread.Sleep(50);
                    }
                    sendTimer++;

                    int availableBytes = spp[0].BytesToRead;
                    if (availableBytes > 0)
                    {
                        bytesReceived = 0;
                        bytesReceived = spp[0].Read(singleReadBuffer, 0, LOCAL_BUFFER_SIZE);

                       // bytesReceived = WidcommAPI.GetData(wdStack, singleReadBuffer);



                        //if we will pass the end of buffer receive till the end then receive the rest
                        /*if ((tail + availableBytes) > this.buffer._Bytes.Length)
                        {
                            bytesReceived = spp.Read(this.buffer._Bytes, tail, this.buffer._Bytes.Length - tail);
                            availableBytes -= bytesReceived;
                            tail = (tail + bytesReceived) % this.buffer._Bytes.Length;
                        }
                        bytesReceived += spp.Read(this.buffer._Bytes, tail, availableBytes);
                        tail = (tail + bytesReceived) % this.buffer._Bytes.Length;*/
                    }

                    Thread.Sleep(30);

                    if (bytesReceived > 0)
                        timeoutIterationsCounter = 0;
                    else
                    {
                        timeoutIterationsCounter++;
                        if (timeoutIterationsCounter > iterationsToTimeout)
                        {
                            spp[0].Close();
                            spp[0].Dispose();
                            //Close();
                            CurrentWockets._LastError = Wockets.Exceptions.ErrorCodes.CONNECTION_TIMEOUT;
                            //this.errorMessage = "MicrosoftBluetoothStream failed at Process(). Disconnection timeout to " + this._HexAddress;
                            this._Status = BluetoothStatus.Disconnected;
                        }

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
                catch (Exception e)
                {
                     
                    spp[0].Close();
                    spp[0].Dispose();
                    this._Status = BluetoothStatus.Disconnected;
                    //Close();
                }
            }
        }
        public bool Close()
        {
            try
            {

                //if ((spp != null) && (spp.IsOpen))
               // {
                    //spp.BaseStream().Close();                                      
                   // spp.Close();
                    //spp.Dispose();    
                                 
               // }
                
               //WidcommAPI.SppRemoveConnection(wdStack);
                //WidcommAPI.DestroyWidcommStack();
                //WidcommAPI.DeleteWidcommStack(wdStack);
               // NetworkStacks._BluetoothStack.Dispose();
               // NetworkStacks._BluetoothStack.Initialize();                
            }
            catch (Exception e)
            {
                CurrentWockets._LastError = Wockets.Exceptions.ErrorCodes.CONNECTION_FAILED_TO_CLOSE;
                //this.errorMessage = "MicrosoftBluetoothStream failed at Close() " + this._HexAddress;
                this._Status = BluetoothStatus.Disconnected;
                return false;
            }
            return true;
        }
    }

}
