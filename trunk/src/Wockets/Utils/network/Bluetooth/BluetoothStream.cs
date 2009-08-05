using System;
using System.Collections.Generic;
using System.Text;
using System.Threading;

namespace Wockets.Utils.network.Bluetooth
{
    public abstract class BluetoothStream
    {
        private const int MAC_SIZE = 6;
        protected byte[] address=null;
        protected string hexAddress=null;
        protected string pin;
        protected BluetoothStatus status;
        protected string errorMessage;
        protected byte[] buffer;
        protected int tail;
        protected const int MAX_DISCONNECTION_COUNTER = 200;
        protected int disconnectionCounter = 0;
        protected Thread processingThread;
        protected Thread reconnectionThread;
        protected List<byte[]> toSend = new List<byte[]>();

        public BluetoothStream(byte[] buffer,byte[] address,string pin)
        {
            this.address = new byte[MAC_SIZE];
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
            this.pin = pin;
            this.buffer = buffer;
            this.tail = 0;
            this.status = BluetoothStatus.Disconnected;
        }

        public int _Tail
        {
            get
            {
                return this.tail;
            }
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

        public void Send(byte[] msg)
        {
            this.toSend.Add(msg);
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
        public abstract bool Open();
        public abstract void Process();
        public abstract bool Close();
    }
}
