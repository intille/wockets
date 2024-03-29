using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Data;
using Wockets.Data.Responses;
using Wockets.Utils;
#if (PocketPC)
using Wockets.Utils.IPC.MMF;
#endif
using System.Threading;

namespace Wockets.Decoders
{
    public abstract class Decoder: XMLSerializable
    {

        #region Serialization Constants
        public const string DECODER_ELEMENT = "DECODER";
        protected const string TYPE_ATTRIBUTE = "type";
        protected const string ID_ATTRIBUTE = "id";
        #endregion Serialization Constants

        
        //format in the MMF file will be as follows
        //full time stamp (4 bytes), X (2 bytes), Y (2 bytes), Z (2 bytes)

       // public DecoderModes _Mode = DecoderModes.DataContinuous;      
        public SensorData[] _Data;
        private SensorData[] response;
        private int size;                
        protected byte[] packet;
        protected int packetPosition;
        private int id;
        private int index;
        private static int IDCounter = 0;
        protected DecoderTypes type;
        protected int head = 0;
        protected int delIndex = 0;
        protected ResponseHandler[] delegates= new ResponseHandler[20];
        protected bool[] subscribed = new bool[] { false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false };
        protected bool cmd = false;


        public int _BufferSize = 0;
        
        public int MaxedoutSamples = 0;

        protected int TotalMaxedout5Minutes = 0;
        protected int TotalSamples5Minutes = 0;

        public int LastMaxedout5Minutes = 0;
        public int LastSamples5Minutes = 0;

        public long TotalMaxedOutSamples = 0;
        public long TotalSamples = 0;

        #if (PocketPC)
        protected MemoryMappedFileStream sdata = null;
        protected MemoryMappedFileStream shead = null;
        protected int sdataSize = 0;       
        public static uint _DUSize = sizeof(short) * 3 + sizeof(double);
        #endif


        public Decoder()
        {
        }
        public Decoder(int bufferSize,int packetSize)
        {


            this.response = new SensorData[10];
            this.size = 0;
            this.packet = new byte[packetSize];
            this.packetPosition = 0;
            this.id = 0;
            this.index = 0;
            this.head = 0;
            this._BufferSize = bufferSize;
           
      
        }

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
        public DecoderTypes _Type
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
        public int _Size
        {
            get
            {
                return this.size;
            }
            set
            {
                this.size = value;
            }
        }



          public SensorData[] _Response
        {
            get
            {
                return this.response;
            }
        }
        #endregion Access Properties

          protected void FireEvent(Response e)
          {
              ThreadPool.QueueUserWorkItem(func =>
              {
                  if (this.subscribed[(int)e._Type])
                      this.delegates[(int)e._Type](e);
              });
          }

        public void Subscribe(ResponseTypes type, ResponseHandler handler)
        {
            this.subscribed[(int)type] = true;
            this.delegates[(int)type] = handler;
        }

        public void Unsubscribe(ResponseTypes type, ResponseHandler handler)
        {
            this.subscribed[(int)type] = false;
        }

        public bool cmdMode
        {
            get
            {
                return this.cmd;
            }
            set
            {
                this.cmd = value;
            }
        }

        public abstract int Decode(int sensorID,byte[] data, int length);
        public abstract int Decode(int sensorID, CircularBuffer data, int start,int end);
        public virtual bool Initialize()
        {
            //if ( (CurrentWockets._Controller._Mode== MemoryMode.BluetoothToLocal) || (CurrentWockets._Controller._Mode== MemoryMode.SharedToLocal))
                this._Data = new SensorData[this._BufferSize];  
#if (PocketPC)
           // else 
            if (CurrentWockets._Controller._Mode == MemoryMode.BluetoothToShared)
            {
                this.sdata = new MemoryMappedFileStream("\\Temp\\wocket" + this._ID + ".dat", "wocket" + this._ID, (_DUSize * (uint)this._BufferSize), MemoryProtection.PageReadWrite);
                this.shead = new MemoryMappedFileStream("\\Temp\\whead" + this._ID + ".dat", "whead" + this._ID, sizeof(int), MemoryProtection.PageReadWrite);
                this.sdataSize = (int)(_DUSize * this._BufferSize);
                this.sdata.MapViewToProcessMemory(0, this.sdataSize);
                this.shead.MapViewToProcessMemory(0, sizeof(int));
                this.shead.Write(BitConverter.GetBytes(this.head), 0, sizeof(int));
                return true;
            }
#endif
            return false;
        }
        public bool Dispose()
        {
#if (PocketPC)
            //if (CurrentWockets._Configuration._MemoryMode == Wockets.Data.Configuration.MemoryConfiguration.SHARED)
            if (CurrentWockets._Controller._Mode== MemoryMode.BluetoothToShared)
            {
                if (this.sdata != null)
                    this.sdata.Close();
                if (this.shead != null)
                    this.shead.Close();
                this._Head = 0;
                this.TotalSamples = 0;
            }
#endif
            return true;
        }

        public delegate void ResponseHandler(object e);
        //Serialization
        public abstract string ToXML();
        public abstract void FromXML(string xml);

        public abstract void Load(ByteReader br);
    }
}

