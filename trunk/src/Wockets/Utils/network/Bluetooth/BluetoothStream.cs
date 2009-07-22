using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Utils.network.Bluetooth
{
    public abstract class BluetoothStream
    {
        private const int MAC_SIZE = 6;
        protected byte[] address;
        protected string pin;
        protected BluetoothStatus status;
        protected string errorMessage;
        protected byte[] buffer;
        protected int tail;

        public BluetoothStream(byte[] buffer)
        {
            this.address = new byte[MAC_SIZE];
            this.pin = "";
            this.buffer = buffer;
            this.tail = 0;
            this.status = BluetoothStatus.Up;           
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
        }
        public byte[] _Address
        {
            get
            {
                return this.address;
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
