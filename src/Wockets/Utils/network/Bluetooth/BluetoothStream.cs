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
        ///// Public Static and constant Definitions

        /// <summary>
        /// Specifies the protocol type for Bluetooth
        /// </summary>
        public static ProtocolType _ProtocolType = (ProtocolType)0x0003;

        /// <summary>
        /// Specifies the Bluetooth address family
        /// </summary>
        public static AddressFamily _AddressFamily = (AddressFamily)32;

        /// <summary>
        /// Specifies the GUID for the serial port service
        /// </summary>
        public static readonly Guid _SerialPort = new Guid(0x00001101, 0x0000, 0x1000, 0x80, 0x00, 0x00, 0x80, 0x5F, 0x9B, 0x34, 0xFB);
        
        /// <summary>
        /// Number of bytes in a bluetooth address
        /// </summary>
        private const int MAC_SIZE = 6;

        /// <summary>
        /// Number of seconds that cause the connection to timout if no data is received, defaults to 12
        /// </summary> 
        private int timeout = 12;

        /// <summary>
        /// Number of milliseconds to poll a stream, defaults to 30 milliseconds
        /// </summary>
        protected int pollingInterval = 30;

        /// <summary>
        /// Based on the _DataTimeout and _PollingTime values, the number of iterations for a connection to timeout is computed
        /// </summary>
        protected int iterationsToTimeout = 400;

        /// <summary>
        /// A counter that stores the number of timeout iterations
        /// </summary>
        protected int timeoutIterationsCounter = 0;

        /// <summary>
        /// Stores the Bluetooth MAC address in a byte array
        /// </summary>
        protected byte[] address=null;

        /// <summary>
        /// Stores the Bluetooth MAC address in Hexadecimal format
        /// </summary>
        protected string hexAddress=null;

        /// <summary>
        /// Stores the pin of the Bluetooth device
        /// </summary>
        protected string pin;
        
        
        /// <summary>
        /// Specifies the status of the Bluetooth connection
        /// </summary>
        public BluetoothStatus _Status;

        /// <summary>
        /// A reference to a circular receive buffer
        /// </summary>
        protected CircularBuffer buffer;


        /// <summary>
        /// A reference to a circular send buffer
        /// </summary>
        protected CircularBuffer sbuffer;

        /// <summary>
        /// A reference to a data processing thread
        /// </summary>
        protected Thread processingThread;

        /// <summary>
        /// A reference to a reconnection thread
        /// </summary>
        protected Thread reconnectionThread;      


        /// <summary>
        /// Specifies if the connection should timeout
        /// </summary>
        public bool _TimeoutEnabled = true;


        public double _ConnectionTime = 0;


        /// <summary>
        /// A class bound lock for critical sections
        /// </summary>
        protected static object mylock;


        [DllImport("FixedPointFFT.dll", EntryPoint = "IsLittleEndian")]
        private static extern int IsLittleEndian();

        public BluetoothStream(CircularBuffer buffer,CircularBuffer sbuffer,byte[] address,string pin)
        {       
            this.address = new byte[MAC_SIZE];
            /*
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
             */
#if (PocketPC)
            if (BitConverter.IsLittleEndian)
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
#else
            if (BitConverter.IsLittleEndian)
            {
                for (int i = 0; i < address.Length; i++)
                    this.address[i] = address[i];
             
            }
            else
            {
                //reverse address depending on the architecture
                for (int i = 0; i < address.Length; i++)
                    this.address[this.address.Length - 1 - i] = address[i];
           
            }
#endif
            this.pin = pin;
            this.buffer = buffer;
            this.sbuffer = sbuffer;
            this._Status = BluetoothStatus.Disconnected;
            mylock = new object();
        }

        /// <summary>
        /// Specifies the numbers of seconds for the connection to timeout, defaults to 12 seconds
        /// </summary>
        public int _Timeout
        {
            get
            {
                return this.timeout;
            }
            set
            {
                if ((pollingInterval > 0) && (timeout > 0))
                {
                    iterationsToTimeout = (value * 1000) / pollingInterval;
                }
                this.timeout = value;
            }
        }

        /// <summary>
        /// Specifies the minimal spacing in milliseconds between consecutive polls for the bluetooth stream
        /// </summary>
        public int _PollingInterval
        {
            get
            {
                return this.pollingInterval;
            }

            set
            {
                if ((pollingInterval > 0) && (timeout > 0))
                {
                    iterationsToTimeout = (value * 1000) / pollingInterval;
                }

                this.pollingInterval = value;
            }
        }


        /// <summary>
        /// Returns the hexadecimal MAC address of the bluetooth stream
        /// </summary>
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


        /// <summary>
        /// Must be overriden by all child classes to read/write to the Bluetooth stream
        /// </summary>
        public abstract void Process();
    }
}
