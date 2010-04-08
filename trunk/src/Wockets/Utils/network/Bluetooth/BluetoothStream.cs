using System;
using System.Collections.Generic;
using System.Text;
using System.Net.Sockets;
using System.Threading;
using System.Runtime.InteropServices;

namespace Wockets.Utils.network.Bluetooth
{
    public abstract class BluetoothStream
    {

        public static ProtocolType _ProtocolType = (ProtocolType)0x0003;
        public static AddressFamily _AddressFamily = (AddressFamily)32;
        public static readonly Guid _SerialPort = new Guid(0x00001101, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
        public TSniff _Tsniff = TSniff.Sniff2Seconds;

        private const int MAC_SIZE = 6;
        protected byte[] address=null;
        protected string hexAddress=null;
        protected string pin;
        protected BluetoothStatus status;
        protected string errorMessage;
        protected CircularBuffer buffer;

        public bool _TimeoutEnabled = true;
        protected const int MAX_DISCONNECTION_COUNTER = 400;
        protected int disconnectionCounter = 0;
        protected Thread processingThread;
        protected Thread reconnectionThread;
        private bool disposed = false;        
        protected CircularBuffer sbuffer;
        protected static object mylock;


        [DllImport("FixedPointFFT.dll", EntryPoint = "IsLittleEndian")]
        private static extern int IsLittleEndian();

        public BluetoothStream(CircularBuffer buffer,CircularBuffer sbuffer,byte[] address,string pin)
        {       
            this.address = new byte[MAC_SIZE];
#if (PocketPC)                       
            if (IsLittleEndian() == 1)
#else
            if (BitConverter.IsLittleEndian)
#endif
            {
                //reverse address depending on the architecture
                for (int i = 0; i < address.Length; i++)
                    this.address[this.address.Length - 1 - i] = address[i];

   

            }
            else
            {


                for (int i = 0; i < address.Length; i++)
                    this.address[i] = address[i];
          



            }
            this.pin = pin;
            this.buffer = buffer;
            this.sbuffer = sbuffer;
            this.status = BluetoothStatus.Disconnected;
            mylock = new object();
        }



        public string _ErrorMessage
        {
            get
            {
                return this.errorMessage;
            }
        }
        public BluetoothStatus _Status
        {
            get
            {
                return this.status;
            }
            set
            {
                this.status = value;
            }
        }
        public byte[] _Address
        {
            get
            {
                return this.address;
            }
        }


        public string _HexAddress
        {
            get
            {
                if (hexAddress == null)
                {
                    string hex = "";
                    for (int i = 0; i < address.Length; i++)                    
                        hex+=address[i].ToString("X2");
                    this.hexAddress = hex;
                }

                return hexAddress;
            }
        }

        public string _Pin
        {
            get
            {
                return this.pin;
            }
        }

        public abstract void Process();

    }
}
