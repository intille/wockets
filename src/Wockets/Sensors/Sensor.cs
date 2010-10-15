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
        /// <summary>
        /// The XML element for the ID tag
        /// </summary>
        protected const string ID_ELEMENT = "ID";

        /// <summary>
        /// The XML element for the Sampling Rate tag
        /// </summary>
        protected const string SR_ELEMENT = "SR";

        /// <summary>
        /// The XML element for the Object tag
        /// </summary>
        protected const string OBJECT_ELEMENT = "OBJECT";

        /// <summary>
        /// The XML element for the Location tag
        /// </summary>
        protected const string LOCATION_ELEMENT = "LOCATION";

        /// <summary>
        /// The XML element for the description tag
        /// </summary>
        protected const string DESCRIPTION_ELEMENT = "DESCRIPTION";

        /// <summary>
        /// The XML element for the calibration tag
        /// </summary>
        protected const string CALIBRATION_ELEMENT = "CALIBRATION";

        /// <summary>
        /// The XML element for the sensor tag
        /// </summary>
        public const string SENSOR_ELEMENT = "SENSOR";

        /// <summary>
        /// The class attribute specifying the class of the sensor MITes, wockets etc.
        /// </summary>
        protected const string CLASS_ATTRIBUTE = "class";


        /// <summary>
        /// The type attribute specifies if the sensor is an accelerometer, gyro etc
        /// </summary>
        protected const string TYPE_ATTRIBUTE = "type";

        /// <summary>
        /// The attribute specifies the ID of the sensor
        /// </summary>
        protected const string ID_ATTRIBUTE = "id";     
   
        /// <summary>
        /// The attribute allows for any text
        /// </summary>
        protected const string TEXT_ATTRIBUTE = "text";
        #endregion Serialization Constants


        /// <summary>
        /// A reference to the decoder associated with this sensor
        /// </summary>
        public Decoder _Decoder;

        /// <summary>
        /// A reference to the receiver associated with this sensor
        /// </summary>
        public Receiver _Receiver;

        /// <summary>
        /// Specifies the class type of the sensor (e.g. wockets, MITes)
        /// </summary>
        public SensorClasses _Class;

        /// <summary>
        /// Specifies the type of the sensors (e.g. accelerometer, gyro... etc)
        /// </summary>
        public SensorTypes _Type;

        /// <summary>
        /// Specifies the root storage directory to save the sensor data
        /// </summary>
        public string _RootStorageDirectory;

        /// <summary>
        /// Specifies the physical location of the sensor
        /// </summary>
        public string _Location;

        /// <summary>
        /// Gives a description of the sensor
        /// </summary>
        public string _Description;

        /// <summary>
        /// Specifies a unique incremental ID from 0 and up to each sensor
        /// </summary>
        public int _ID;

        /// <summary>
        /// Specifies the expected sampling rate of the sensor
        /// </summary>
        public int _SamplingRate;


        public bool _Flush=false;

        /// <summary>
        /// Specifies if the sensor is saving data or not. True means it should save, false means it shouldnt
        /// </summary>
        public bool _Saving;

        /// <summary>
        /// The number of saved packets so far
        /// </summary>
        public int _SavedPackets = 0; 

        /// <summary>
        /// The number of received packets so far
        /// </summary>
        public int _ReceivedPackets = 0;

        public int _ReceivedACs = 0;
        public int _TotalReceivedACs = 0;

        public int _SavedACs = 0;
        public int _TotalSavedACs = 0;

        public int _Full = 0;

        public int _Partial = 0;

        public int _Empty = 0;

        public string _Address = "";
        /// <summary>
        /// Specifies if the sensor is enabled or not
        /// </summary>
        public bool _Loaded = false;

        public SensorModes _Mode = SensorModes.Data;

        public int _BatteryLevel = 0;

        public int _BatteryPercent = 0;
        
        public int _PDUCount = 0;

        /// <summary>
        /// A constructor that initializes the sensor type and class
        /// </summary>
        /// <param name="type"></param>
        /// <param name="classname"></param>
        public Sensor(SensorTypes type,SensorClasses classname)
        {
            this._Class = classname;
            this._Type = type;
            this._SamplingRate = 0;
            this._Saving = true;
        }


        /// <summary>
        /// Compares 2 sensors based on ID, used for sorting a list of sensors
        /// </summary>
        /// <param name="sensor">another sensor</param>
        /// <returns>0 if equal, otherwise an int</returns>
        public int CompareTo(object sensor)
        {
            return this._ID.CompareTo(((Sensor)sensor)._ID);
        }


        /// <summary>
        /// Serializes sensor specifications into an xml
        /// </summary>
        /// <param name="innerXML">embed the xml into the output</param>
        /// <returns>An xml serialized sensor string</returns>
        protected string ToXML(string innerXML)
        {
            string xml = "<" + SENSOR_ELEMENT + " " +
            CLASS_ATTRIBUTE + "=\"" + this._Class.ToString("g") + "\" " +
            TYPE_ATTRIBUTE + "=\"" + this._Type.ToString("g") + "\">\n";            
            xml += "<" + ID_ELEMENT + " " + ID_ATTRIBUTE + "=\"" +
                this._ID + "\"></" + ID_ELEMENT + ">\n";
            xml += "<" + SR_ELEMENT + " " + TEXT_ATTRIBUTE + "=\"" +
               this._SamplingRate + "\"></" + SR_ELEMENT + ">\n";
            xml += "<" + OBJECT_ELEMENT + " " + TEXT_ATTRIBUTE + "=\"\"></" +
                OBJECT_ELEMENT + ">\n";
            xml += "<" + LOCATION_ELEMENT + " " + TEXT_ATTRIBUTE + "=\"" +
                this._Location + "\"></" + LOCATION_ELEMENT + ">\n";
            xml += "<" + DESCRIPTION_ELEMENT + " " + TEXT_ATTRIBUTE +
                "=\"" + this._Description + "\"></" + DESCRIPTION_ELEMENT + ">\n";
            xml += "<" + Receiver.RECEIVER_ELEMENT + " " + ID_ATTRIBUTE +
          "=\"" + this._Receiver._ID + "\"></" + Receiver.RECEIVER_ELEMENT + ">\n";
            xml += "<" + Decoder.DECODER_ELEMENT + " " + ID_ATTRIBUTE +
         "=\"" + this._Decoder._ID + "\"></" + Decoder.DECODER_ELEMENT + ">\n";
            xml += innerXML;
            xml += "</" + SENSOR_ELEMENT + ">\n";
            return xml;
        }

        /// <summary>
        /// An abstract method to serialize the sensor into an xml
        /// </summary>
        /// <returns>An XML string describing the sensor</returns>
        public abstract string ToXML();

        /// <summary>
        /// An abstract method to save the sensor data
        /// </summary>
        public abstract void Save();        

        /// <summary>
        /// An abstract method that loads a sensor value once at a time
        /// </summary>
        /// <returns>True on success, otherwise false</returns>
        public abstract bool Load();

        /// <summary>
        /// An abstract method that releases and disposes any resources associated with the sensor
        /// </summary>
        public abstract void Dispose();


        /// <summary>
        /// A method that populates a sensor object from an XML string
        /// </summary>
        /// <param name="xml">An input XML string that describes the sensor</param>
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
                        else if ((jNode.Name == Receiver.RECEIVER_ELEMENT) && (jAttribute.Name == ID_ATTRIBUTE))
                        {
                            this._Receiver = new Receivers.GenericReceiver();
                            this._Receiver._ID = Convert.ToInt32(jAttribute.Value);
                        }
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
