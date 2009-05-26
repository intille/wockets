using System;
using System.Collections.Generic;
using System.Collections;
using System.Text;
using System.Xml;
using Wockets.Utils;
using Wockets.Sensors.Accelerometers;

namespace Wockets.Sensors
{
    public sealed class SensorList: List<Sensor>,XMLSerializable
    {
        #region Serialization Constants
        public const string SENSORS_ELEMENT = "SENSORS";
        private const string CLASS_ATTRIBUTE = "class";
        private const string TYPE_ATTRIBUTE = "type";
        #endregion Serialization Constants

        public SensorList()
        {
        }

        public string ToXML()
        {
            string xml = "<" + SENSORS_ELEMENT + ">\n";
            for (int i=0;(i<this.Count);i++)
                xml += this[i].ToXML();
            xml += "</" + SENSORS_ELEMENT + ">\n";            
            return xml;
        }

        public void FromXML(string xml)
        {
            XmlDocument dom = new XmlDocument();
            dom.LoadXml(xml);
            XmlNode xNode = dom.DocumentElement;

            if ((xNode.Name == SENSORS_ELEMENT) && (xNode.HasChildNodes))
            {
                foreach (XmlNode jNode in xNode.ChildNodes)
                {
                    if (jNode.Name == Sensor.SENSOR_ELEMENT)
                    {
                        SensorClasses sensorClass=SensorClasses.Unknown;
                        SensorTypes sensorType=SensorTypes.UNKNOWN;
                        foreach (XmlAttribute jAttribute in jNode.Attributes)
                        {
                            if (jAttribute.Name == CLASS_ATTRIBUTE)
                                sensorClass= (SensorClasses)Enum.Parse(typeof(SensorClasses), jAttribute.Value, true);
                            else if (jAttribute.Name == TYPE_ATTRIBUTE)
                                sensorType = (SensorTypes)Enum.Parse(typeof(SensorTypes), jAttribute.Value, true);
                        }

                        if (sensorType == SensorTypes.ACCEL)
                        {
                            Sensor sensor=null;
#if (PocketPC)
                            if (sensorClass == SensorClasses.HTCDiamondTouch)
                                sensor = new HTCDiamondTouch();
                            else 
#endif                            
                            if (sensorClass == SensorClasses.MITes)
                                sensor = new MITe();
                            else if (sensorClass == SensorClasses.Sparkfun)
                                sensor = new Sparkfun();
                            else if (sensorClass == SensorClasses.Wockets)
                                sensor = new Wocket();                                                            
                            sensor.FromXML(jNode.OuterXml);
                             this.Insert(sensor._ID,sensor);
                        }
                    }
                }

            }
        }
    }
}
