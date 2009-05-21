using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Utils;

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
        private bool isRunning;
        private byte[] buffer;
        private int maximumSamplingRate;
        private int id;
        protected ReceiverTypes type;

        public Receiver()
        {
            this.isRunning = false;
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


        public byte[] _Buffer
        {
            get
            {
                return this.buffer;
            }
            set
            {
                this.buffer = value;
            }
        }
        
        public bool _Running
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

        public abstract bool Initialize();
        public abstract int Read();
        public abstract void Write(byte[] data,int length);
        public abstract bool Dispose();

        //Serialization
        public abstract string ToXML();
        public abstract void FromXML(string xml);


        public abstract int CompareTo(object receiver);
    }
}
