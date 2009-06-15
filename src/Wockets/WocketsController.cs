using System;
using System.Collections.Generic;
using System.Xml;
using System.Collections;
using Wockets.Receivers;
using Wockets.Decoders;
using Wockets.Sensors;
using Wockets.Utils;

namespace Wockets
{
    public sealed class WocketsController : XMLSerializable
    {
        #region Serialization Constants
        private const string SENSORDATA_ELEMENT = "SENSORDATA";
        #endregion Serialization Constants
            
        private DecoderList decoders;
        private ReceiverList receivers;
        private SensorList sensors;

        private string description;
        private string filename;
        private string name;

        public WocketsController(string name,string filename,string description)
        {
            this.decoders = new DecoderList();
            this.receivers = new ReceiverList();
            this.sensors = new SensorList();
            this.name =name;
            this.filename =filename;
            this.description = description;
        }

        public string _Name
        {
            get
            {
                return this.name;
            }
            set
            {
                this.name = value;
            }
        }

        public string _FileName
        {
            get
            {
                return this.filename;
            }
            set
            {
                this.filename = value;
            }
        }

        public string _Description
        {
            get
            {
                return this.description;
            }

            set
            {
                this.description = value;
            }
        }
        public DecoderList _Decoders
        {
            get
            {                         
                return this.decoders;
            }
            set
            {
                this.decoders = value;
            }
        }

        public ReceiverList _Receivers
        {
            get
            {
                return this.receivers;
            }
            set
            {
                this.receivers = value;
            }
        }

        public SensorList _Sensors
        {
            get
            {
                return this.sensors;
            }

            set
            {
                this.sensors = value;
            }
        }

        #region Serialization Methods
        public string ToXML()
        {
            string xml = "<" + SENSORDATA_ELEMENT + ">\n";
            xml += this.receivers.ToXML();
            xml += this.decoders.ToXML();
            xml += this.sensors.ToXML();
            xml += "</" + SENSORDATA_ELEMENT + ">\n";
            return xml;
        }

        public void FromXML(string xml)
        {
            XmlDocument dom = new XmlDocument();
            dom.Load(xml);
            XmlNode xNode = dom.DocumentElement;

            if ((xNode.Name == SENSORDATA_ELEMENT) && (xNode.HasChildNodes))
            {
                foreach (XmlNode jNode in xNode.ChildNodes)
                {
                    if (jNode.Name == ReceiverList.RECEIVERS_ELEMENT)
                        this.receivers.FromXML(jNode.OuterXml);
                    else if (jNode.Name == DecoderList.DECODERS_ELEMENT)
                        this.decoders.FromXML(jNode.OuterXml);
                    else if (jNode.Name == SensorList.SENSORS_ELEMENT)
                    {
                        //the sensor by default loads with a generic decoder as a place holder with its ID set
                        //to point to the right decoder in this.decoders
                        this.sensors.FromXML(jNode.OuterXml);

                        //the decoder references for the sensor have to be updated correctly
                        for (int i = 0; (i < this.sensors.Count); i++)
                            this.sensors[i]._Decoder = this.decoders[this.sensors[i]._Decoder._ID];
                    }
                }
            }
        }
        #endregion Serialization Methods
    }
}
