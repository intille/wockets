using System;
using System.Collections.Generic;
using System.Text;
using System.Threading;

namespace Wockets.Utils.network.Bluetooth
{
    public abstract class BluetoothStream : IDisposable
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
        private bool disposed = false;
        //protected List<byte[]> toSend = new List<byte[]>();
        protected CircularBuffer sbuffer;
        //private bool disposed = false;
        protected static object mylock;

      

        public BluetoothStream(byte[] buffer,CircularBuffer sbuffer,byte[] address,string pin)
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
            this.sbuffer = sbuffer;
            this.status = BluetoothStatus.Disconnected;
            mylock = new object();
        }

        /*
         // Use C# destructor syntax for finalization code.
        // This destructor will run only if the Dispose method
        // does not get called.
        // It gives your base class the opportunity to finalize.
        // Do not provide destructors in types derived from this class.
        ~BluetoothStream()
        {
            // Do not re-create Dispose clean-up code here.
            // Calling Dispose(false) is optimal in terms of
            // readability and maintainability.
            Dispose(false);
        }*/

        // Implement IDisposable.
        // Do not make this method virtual.
        // A derived class should not be able to override this method.
        public void Dispose()
        {
            Dispose(true);
            // This object will be cleaned up by the Dispose method.
            // Therefore, you should call GC.SupressFinalize to
            // take this object off the finalization queue
            // and prevent finalization code for this object
            // from executing a second time.
            GC.SuppressFinalize(this);
        }

        // Dispose(bool disposing) executes in two distinct scenarios.
        // If disposing equals true, the method has been called directly
        // or indirectly by a user's code. Managed and unmanaged resources
        // can be disposed.
        // If disposing equals false, the method has been called by the
        // runtime from inside the finalizer and you should not reference
        // other objects. Only unmanaged resources can be disposed.
        protected virtual void Dispose(bool disposing)
        {
            // Check to see if Dispose has already been called.
            if (!this.disposed)
            {
                // If disposing equals true, dispose all managed
                // and unmanaged resources.
                if (disposing)
                {
                    // Dispose managed resources.
                    //processingThread.Join();
                    //processingThread= null;
                }

                // Call the appropriate methods to clean up
                // unmanaged resources here.
                // If disposing is false,
                // only the following code is executed.
                

                // Note disposing has been done.
                disposed = true;

            }
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

        /*public void Send(byte[] msg)
        {
            lock (this.toSend)
            {
                this.toSend.Add(msg);
            }
        }*/

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
        //public abstract bool Close();
    }
}
