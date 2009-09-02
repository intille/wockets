using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Utils;
using System.Threading;

namespace Wockets.Receivers
{
    public abstract class Receiver : XMLSerializable, IComparable
    {
        #region Serialization Constants
        public const string RECEIVER_ELEMENT = "RECEIVER";
        protected const string ID_ATTRIBUTE = "id";
        protected const string TYPE_ATTRIBUTE = "type";
        protected const string BUFFERSIZE_ATTRIBUTE = "BufferSize";
        protected const string MAX_SR_ATTRIBUTE = "MaxSR";
        #endregion Serialization Constants
        protected bool isRunning;
        private bool isReconnecting;
        //public byte[] _Buffer;
        public CircularBuffer _Buffer;
        protected int head;
        private int maximumSamplingRate;
        private int id;
        protected ReceiverTypes type;
        protected Thread reconnectionThread=null;
        protected int disconTime=0;
        protected long lastTime;
        protected int ndisc = 0;
        protected int disconCount=0;

        public Receiver(int bufferSize)
        {
            //this.isRunning = false;
            //this.isReconnecting = false;
            //this._Buffer= new byte[bufferSize];
            this._Buffer = new CircularBuffer(bufferSize);


            this.head = 0;

            this.status = ReceiverStatus.Disconnected;
        }

        /*
        public Receiver(int id, int bufferSize,int max_sr)
        {
            this.isRunning = false;
            this.buffer = new byte[bufferSize];
            this.maximumSamplingRate = max_sr;
        }
        */

        #region Access Properties
        public int _Head
        {
            get
            {
                return this.head;
            }
            set
            {
                this.head = value;
            }
        }

        public int _ID
        {
            get
            {
                return this.id;
            }

            set
            {
                this.id = value;
            }
        }

        public ReceiverTypes _Type
        {
            get
            {
                return this.type;
            }

            set
            {
                this.type = value;
            }
        }


    
        /*public byte[] _Buffer
        {
            get
            {
                return this.buffer;
            }
            set
            {
                this.buffer = value;
            }
        }*/
        
        public virtual bool _Running
        {
            get
            {
                return this.isRunning;
            }
            set
            {
                this.isRunning = value;
            }
        }

        public int NumDisconnect
        {
            get
            {
                return this.ndisc;
            }
            set
            {
                this.ndisc = value;
            }
        }

        public int TimeDisconnect
        {
            get
            {
                if (this.disconTime > 0)
                    return this.disconTime;
                else
                    return 0;
            }
            set
            {
                this.disconTime = value;
            }
        }

        public int Disconnected
        {
            get
            {
                return this.disconCount;
            }

            set
            {
                this.disconCount = value;
            }
        }


        protected ReceiverStatus status;
        public virtual ReceiverStatus _Status
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
        public int _MaximumSamplingRate
        {
            get
            {
                return this.maximumSamplingRate;
            }
            set
            {
                this.maximumSamplingRate = value;
            }
        }
        #endregion Access Properties

        public abstract int _Tail
        {
            get;
        }
        public abstract bool Initialize();        
        public abstract bool Dispose();
        public abstract void Update();


        //Serialization
        public abstract string ToXML();
        public abstract void FromXML(string xml);


        public abstract int CompareTo(object receiver);
        
    }
}
