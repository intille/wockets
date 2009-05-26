using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Data;
using Wockets.Utils;

namespace Wockets.Decoders
{
    public abstract class Decoder: XMLSerializable
    {

        #region Serialization Constants
        public const string DECODER_ELEMENT = "DECODER";
        protected const string TYPE_ATTRIBUTE = "type";
        protected const string ID_ATTRIBUTE = "id";
        #endregion Serialization Constants


        private SensorData[] data;
        private int size;                
        protected byte[] packet;
        protected int packetPosition;
        private int id;
        private static int IDCounter = 0;
        public Decoder(int bufferSize,int packetSize)
        {
            this.data = new SensorData[bufferSize];
            this.size = 0;
            this.packet = new byte[packetSize];
            this.packetPosition = 0;
            this.id = IDCounter++;
        }

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

        public SensorData[] _Data
        {
            get
            {
                return this.data;
            }
        }
        #endregion Access Properties

        public abstract int Decode(int sensorID,byte[] data, int length);
        //public abstract bool IsValid(SensorData data);

        //Serialization
        public abstract string ToXML();
        public abstract void FromXML(string xml);
    }
}
