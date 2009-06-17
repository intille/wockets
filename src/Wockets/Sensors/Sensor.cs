using System;
using System.Collections.Generic;
using System.Xml;
using Wockets.Receivers;
using Wockets.Decoders;
using Wockets.Utils;

namespace Wockets.Sensors
{
    public abstract class Sensor : XMLSerializable, IComparable
    {
        #region Serialization Constants
        protected const string ID_ELEMENT = "ID";
        protected const string SR_ELEMENT = "SR";
        protected const string CHANNEL_ELEMENT = "CHANNEL";
        protected const string OBJECT_ELEMENT = "OBJECT";
        protected const string LOCATION_ELEMENT = "LOCATION";
        protected const string DESCRIPTION_ELEMENT = "DESCRIPTION";
        protected const string CALIBRATION_ELEMENT = "CALIBRATION";
        public const string SENSOR_ELEMENT = "SENSOR";


        protected const string CLASS_ATTRIBUTE = "class";
        protected const string TYPE_ATTRIBUTE = "type";
        protected const string ID_ATTRIBUTE = "id";        
        protected const string TEXT_ATTRIBUTE = "text";
        #endregion Serialization Constants

        private Decoder decoder;
        private int receiver;
        private SensorClasses classname;
        private SensorTypes type;
        private string rootStorageDirectory;
        private string location;
        private string description;
        private int id;
        private int sr;
        private int actSR;
        private bool saving;

        public Sensor(SensorTypes type,SensorClasses classname)
        {
            this.classname = classname;
            this.type = type;
            this.sr = 0;
            this.saving = false;
        }
        /*
        public Sensor(int id, SensorClasses classname, SensorTypes type, string location, string description)
        {
            this.id = id;
            this.classname = classname;
            this.type = type;
            this.location = location;
            this.description = description;
        }*/

        public int CompareTo(object sensor)
        {
            return this.id.CompareTo(((Sensor)sensor)._ID);
        }

        public bool _Saving
        {
            get
            {
                return this.saving;
            }
            set
            {
                this.saving = value;
            }
        }
        public int _SamplingRate
        {
            get
            {
                return this.sr;
            }
            set
            {
                this.sr = value;
            }
        }

        public void setSR(int i)
        {
            this.actSR = i;
        }

        public int getSR()
        {
            return this.actSR;
        }
        /*
        public int _Channel
        {
            get
            {
                return this.channel;
            }
            set
            {
                this.channel = value;
            }
        }*/

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

        public SensorClasses _Class
        {
            get
            {
                return this.classname;
            }
            set
            {
                this.classname = value;
            }
        }

        public SensorTypes _Type
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

        public string _RootStorageDirectory
        {
            get
            {
                return this.rootStorageDirectory;
            }

            set
            {
                this.rootStorageDirectory = value;
            }
        }

        public string _Location
        {
            get
            {
                return this.location;
            }

            set
            {
                this.location = value;
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

        public Decoder _Decoder
        {
            get
            {
                return this.decoder;
            }
            set
            {
                this.decoder = value;
            }
        }

        public int _Receiver
        {
            get
            {
                return this.receiver;
            }
            set
            {
                this.receiver = value;
            }
        }

        protected string ToXML(string innerXML)
        {
            string xml = "<" + SENSOR_ELEMENT + " " +
            CLASS_ATTRIBUTE + "=\"" + this.classname.ToString("g") + "\" " +
            TYPE_ATTRIBUTE + "=\"" + this.type.ToString("g") + "\">\n";            
            xml += "<" + ID_ELEMENT + " " + ID_ATTRIBUTE + "=\"" +
                this.id + "\"></" + ID_ELEMENT + ">\n";
            xml += "<" + SR_ELEMENT + " " + TEXT_ATTRIBUTE + "=\"" +
               this.sr + "\"></" + SR_ELEMENT + ">\n";
            /*
            xml += "<" + CHANNEL_ELEMENT + " " + ID_ATTRIBUTE + "=\"" +
             this.channel+ "\"></" + CHANNEL_ELEMENT + ">\n";*/
            xml += "<" + OBJECT_ELEMENT + " " + TEXT_ATTRIBUTE + "=\"\"></" +
                OBJECT_ELEMENT + ">\n";
            xml += "<" + LOCATION_ELEMENT + " " + TEXT_ATTRIBUTE + "=\"" +
                this.location + "\"></" + LOCATION_ELEMENT + ">\n";
            xml += "<" + DESCRIPTION_ELEMENT + " " + TEXT_ATTRIBUTE +
                "=\"" + this.description + "\"></" + DESCRIPTION_ELEMENT + ">\n";
            xml += "<" + Receiver.RECEIVER_ELEMENT + " " + ID_ATTRIBUTE +
          "=\"" + this.receiver + "\"></" + Receiver.RECEIVER_ELEMENT + ">\n";
            xml += "<" + Decoder.DECODER_ELEMENT + " " + ID_ATTRIBUTE +
         "=\"" + this.decoder + "\"></" + Decoder.DECODER_ELEMENT + ">\n";
            xml += innerXML;
            xml += "</" + SENSOR_ELEMENT + ">\n";
            return xml;
        }

        public abstract string ToXML();

        public abstract void Save();

        // this method loads the data from saved files one sample at a time
        //and populates the decoder
        public abstract bool Load();

        public abstract void Dispose();

        public virtual void FromXML(string xml)
        {
            XmlDocument dom = new XmlDocument();
            dom.LoadXml(xml);
            XmlNode iNode = dom.DocumentElement;
            if (iNode.Name == SENSOR_ELEMENT)
            {

                foreach (XmlAttribute iAttribute in iNode.Attributes)
                {
                    if (iAttribute.Name == CLASS_ATTRIBUTE)
                        this._Class =  (SensorClasses)Enum.Parse(typeof(SensorClasses), iAttribute.Value,true);
                    else if (iAttribute.Name == TYPE_ATTRIBUTE)
                        this._Type = (SensorTypes)Enum.Parse(typeof(SensorTypes), iAttribute.Value,true);
                }

                foreach (XmlNode jNode in iNode.ChildNodes)
                {
                    foreach (XmlAttribute jAttribute in jNode.Attributes)
                    {
                        if ((jNode.Name == ID_ELEMENT) && (jAttribute.Name == ID_ATTRIBUTE))
                            this._ID = Convert.ToInt32(jAttribute.Value);
                        else if ((jNode.Name == SR_ELEMENT) && (jAttribute.Name == TEXT_ATTRIBUTE))
                            this._SamplingRate = Convert.ToInt32(jAttribute.Value);
                        /*else if ((jNode.Name == CHANNEL_ELEMENT) && (jAttribute.Name == ID_ATTRIBUTE))
                            this._Channel = Convert.ToInt32(jAttribute.Value);*/
                        else if ((jNode.Name == Receiver.RECEIVER_ELEMENT) && (jAttribute.Name == ID_ATTRIBUTE))
                            this._Receiver = Convert.ToInt32(jAttribute.Value);
                        else if ((jNode.Name == Decoder.DECODER_ELEMENT) && (jAttribute.Name == ID_ATTRIBUTE))
                        {
                            this._Decoder = new Decoders.Accelerometers.GenericDecoder();
                            this._Decoder._ID = Convert.ToInt32(jAttribute.Value);
                        }
                        else if ((jNode.Name == LOCATION_ELEMENT) && (jAttribute.Name == TEXT_ATTRIBUTE))
                            this._Location = jAttribute.Value;
                        else if ((jNode.Name == DESCRIPTION_ELEMENT) && (jAttribute.Name == TEXT_ATTRIBUTE))
                            this._Description = jAttribute.Value;

                    }
                }
            }
        }
    }
}
