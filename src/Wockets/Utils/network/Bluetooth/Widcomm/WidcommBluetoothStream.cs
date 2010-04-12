using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Utils.network.Bluetooth;
using System.IO.Ports;
using System.Threading;
using System.Globalization;
using Microsoft.Win32; 

namespace Wockets.Utils.network.Bluetooth.Widcomm
{
    public class WidcommBluetoothStream : BluetoothStream
    {
        private int comPort = 0;
        private SerialPort spp = null;
        private IntPtr wdStack;
        private static int x = 0;
        public string _COMPORT = "";
        public WidcommBluetoothStream(CircularBuffer buffer, CircularBuffer sbuffer, byte[] address, string pin)
            : base(buffer, sbuffer, address, pin)
        {
            
            //this.wdStack = WidcommAPI.CreateWidcommStack();
            //WidcommAPI.SetAutoReconnect(this.wdStack);  
            if (this._HexAddress.IndexOf("A0") >= 0)
                _COMPORT = "BTC3";
            else
                _COMPORT = "BTC2";
        }

        public bool Open()
        {
            try
            {
                if (this.spp == null)
                {
                    if (processingThread != null)
                        processingThread.Abort();

                    long bt_address = long.Parse(this._HexAddress, NumberStyles.HexNumber, CultureInfo.CurrentCulture.NumberFormat);
                    //comPort = ((WidcommBluetoothStack)NetworkStacks._BluetoothStack).OpenSPP(bt_address);
                    //spp = new SerialPort("COM" + comPort, 38400, Parity.None, 8, StopBits.One);
                    //spp.Open();
                    // int r=WidcommAPI.Bond(((WidcommBluetoothStack)NetworkStacks._BluetoothStack)._Reference, bt_address, "1234");
                    //Hashtable h=((WidcommBluetoothStack)NetworkStacks._BluetoothStack).Search();

                    //RegistryKey rk = Registry.LocalMachine.OpenSubKey("SOFTWARE\\WIDCOMM\\BTConfig\\Applications\\0001", true);
                    //rk.ge
                    // if (x == 0)
                    //rk.SetValue("ComPortNumber", 7, RegistryValueKind.DWord);
                    //else
                    //  rk.SetValue("ComPortNumber", 9, RegistryValueKind.DWord);
                    //rk.Close();
                    //this.wdStack = WidcommAPI.CreateWidcommStack();
                    // WidcommAPI.SetAutoReconnect(this.wdStack);
                    int r = WidcommAPI.SppCreateConnection(((WidcommBluetoothStack)NetworkStacks._BluetoothStack)._Reference, (byte)1, bt_address);
                    int retry = 0;
                    
                    while (retry < 5)
                    {
                        System.Threading.Thread.Sleep(500);
                        comPort = WidcommAPI.SppComPort(((WidcommBluetoothStack)NetworkStacks._BluetoothStack)._Reference);
                        if (comPort > 0)
                            break;
                        retry++;
                    }

                    

                   comPort = 3;

                    // if (x == 0)
                    //{
                   spp = new SerialPort(_COMPORT, 38400, Parity.None, 8, StopBits.One);                    
                    if (!spp.IsOpen)
                        spp.Open();
                    this._Status = BluetoothStatus.Connected;
                    //start the processing thread
                    processingThread = new Thread(new ThreadStart(Process));
                    processingThread.Start();
                    x++;
                    //}

                }
            }
            catch (Exception e)
            {
                CurrentWockets._LastError = Wockets.Exceptions.ErrorCodes.CONNECTION_FAILED_TO_OPEN;
                CurrentWockets._LastErrorMessage = "MicrosoftBluetoothStream failed at Open() " + this._HexAddress;

                this._Status = BluetoothStatus.Disconnected;
                return false;
            }
            return true;
        }

        private const int LOCAL_BUFFER_SIZE = 2048;
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
                        spp.Write(sendByte, 0, 1);
                        sendTimer = 0;
                        Thread.Sleep(50);
                    }
                    sendTimer++;

                    int availableBytes = spp.BytesToRead;
                    if (availableBytes > 0)
                    {
                        bytesReceived = 0;
                        bytesReceived = spp.Read(singleReadBuffer, 0, LOCAL_BUFFER_SIZE);
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
                    this._Status = BluetoothStatus.Disconnected;
                }
            }
        }
        public bool Close()
        {
            try
            {
                if (this.spp != null)
                    this.spp.Close();
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
