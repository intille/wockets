using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using System.Xml.Schema;
using System.Collections;

namespace SXML
{
    public class Reader
    {
        public const string DEFAULT_XML_FILE = "SensorData.xml";
        public const string DEFAULT_XSD_FILE = "SensorData.xsd";

        private string xmlFile;
        private string xsdFile;


        public Reader(string masterDirectory, string dataDirectory)
        {
            this.xmlFile = dataDirectory +"\\"+ DEFAULT_XML_FILE;
            this.xsdFile = masterDirectory + DEFAULT_XSD_FILE;
        }

        public SensorAnnotation parse(int maxReceivers)
        {
            SensorAnnotation annotation = new SensorAnnotation(maxReceivers);
            XmlDocument dom = new XmlDocument();
            dom.Load(this.xmlFile);
            XmlNode xNode = dom.DocumentElement;
            bool[] countedReceiver = new bool[maxReceivers];
            bool firstAccel = false;

            for (int i = 0; (i < maxReceivers); i++)
                countedReceiver[i] = false;

            if ((xNode.Name == Constants.SENSORDATA_ELEMENT) && (xNode.HasChildNodes))
            {
                
                foreach (XmlAttribute xAttribute in xNode.Attributes)                
                {                                            
                    if (xAttribute.Name == Constants.DATASET_ATTRIBUTE)                    
                    {                    
                        annotation.Dataset = xAttribute.Value;                        
                    }                    
                }

                //Sensor nodes
                foreach (XmlNode iNode in xNode.ChildNodes) 
                {


                    if (iNode.Name == Constants.RECEIVERS_ELEMENT)
                    {
                        foreach (XmlNode jNode in iNode.ChildNodes)
                        {
                            

                            if (jNode.Name == Constants.RECEIVER_ELEMENT)
                            {
                                Receiver receiver = new Receiver();
                                foreach (XmlAttribute iAttribute in jNode.Attributes)
                                {
                                    //read nodes attributes
                                    if (iAttribute.Name == Constants.ID_ATTRIBUTE)
                                    {
                                        receiver.ID = Convert.ToInt32(iAttribute.Value);
                                    }
                                    else if (iAttribute.Name == Constants.TYPE_ATTRIBUTE)
                                    {
                                        receiver.Type = iAttribute.Value;
                                        if (receiver.Type == Constants.RECEIVER_BLUETOOTH)
                                            annotation.TotalBluetoothReceivers++;
                                        else if (receiver.Type == Constants.RECEIVER_USB)
                                            annotation.TotalWiredReceivers++;
                                    }
                                    else if (iAttribute.Name == Constants.PASSKEY_ATTRIBUTE)
                                    {
                                        receiver.PassKey = iAttribute.Value;
                                    }
                                    else if (iAttribute.Name == Constants.DECODER_ATTRIBUTE)
                                    {
                                        receiver.Decoder = iAttribute.Value;
                                    }
                                    else if (iAttribute.Name == Constants.MAC_ATTRIBUTE)
                                    {
                                        receiver.MAC = iAttribute.Value;

                                        for (int i = 0; (i < Constants.MAC_SIZE); i++)
                                            receiver.MacAddress[i] = (byte)(System.Int32.Parse(iAttribute.Value.Substring(i * 2, 2), System.Globalization.NumberStyles.AllowHexSpecifier) & 0xff);
                                    }
                                }
                                annotation.Receivers.Add(receiver);
                                annotation.TotalReceivers++;
                            }
                        }
                    }
                    //Backward compatibility
                    else if (iNode.Name == Constants.SENSOR_ELEMENT)
                    {
                        Sensor sensor = new Sensor();

                        foreach (XmlAttribute iAttribute in iNode.Attributes)
                        {
                            //read nodes attributes
                            if (iAttribute.Name == Constants.CLASS_ATTRIBUTE)
                            {
                                sensor.SensorClass = iAttribute.Value;
                            }
                            else if (iAttribute.Name == Constants.TYPE_ATTRIBUTE)
                            {
                                sensor.Type = iAttribute.Value;
                            }
                        }


                        foreach (XmlNode jNode in iNode.ChildNodes)
                        {
                            //Console.WriteLine(jNode.Name);

                            foreach (XmlAttribute jAttribute in jNode.Attributes)
                            {
                                //read nodes attributes
                                if ((jNode.Name == Constants.ID_ELEMENT) && (jAttribute.Name == Constants.ID_ATTRIBUTE))
                                {
                                    sensor.ID = jAttribute.Value;

                                    //if this is an HR sensor
                                    if (Convert.ToInt32(jAttribute.Value) == 0)
                                    {
                                        annotation.IsHR = true;
                                    }
                                    if ((firstAccel == false) && (Convert.ToInt32(jAttribute.Value) > 0))
                                    {
                                        annotation.FirstAccelerometer = Convert.ToInt32(jAttribute.Value);
                                        firstAccel = true;
                                    }

                                    if (annotation.MaximumSensorID < Convert.ToInt32(jAttribute.Value))
                                        annotation.MaximumSensorID = Convert.ToInt32(jAttribute.Value);

                                }
                                else if ((jNode.Name == Constants.OBJECT_ELEMENT) && (jAttribute.Name == Constants.TEXT_ATTRIBUTE))
                                {
                                    sensor.SensorObject = jAttribute.Value;
                                }
                                else if ((jNode.Name == Constants.RECEIVER_ELEMENT) && (jAttribute.Name == Constants.ID_ATTRIBUTE))
                                {
                                    int receiver_id = Convert.ToInt32(jAttribute.Value);
                                    if ((receiver_id < maxReceivers) && (receiver_id >= 0))
                                    {
                                        annotation.NumberSensors[receiver_id] = annotation.NumberSensors[receiver_id] + 1;
                                        sensor.Receiver = jAttribute.Value;
                                        if (countedReceiver[receiver_id] == false)
                                        {
                                          annotation.TotalReceivers++;
                                         countedReceiver[receiver_id] = true;
                                        }
                                    }
                                    else
                                        throw new Exception("Receiver in sensor file out of bound");

                                    //sensor.Receiver = jAttribute.Value;                                                                        
                                    //if (Convert.ToInt32(sensor.Receiver) == 1)
                                    //{
                                    //    annotation.SensorCount1++;
                                    //}
                                    //else if (Convert.ToInt32(sensor.Receiver) == 2)
                                    //{
                                    //    annotation.SensorCount2++;
                                    //}
                                }
                                else if ((jNode.Name == Constants.LOCATION_ELEMENT) && (jAttribute.Name == Constants.TEXT_ATTRIBUTE))
                                {
                                    sensor.Location = jAttribute.Value;
                                }
                                else if ((jNode.Name == Constants.DESCRIPTION_ELEMENT) && (jAttribute.Name == Constants.TEXT_ATTRIBUTE))
                                {
                                    sensor.Description = jAttribute.Value;
                                }
                                else if ((jNode.Name == Constants.DESCRIPTION_ELEMENT) && (jAttribute.Name == Constants.SR_ATTRIBUTE))
                                {
                                    sensor.SamplingRate = 12; //TODO
                                }
                                else if ((jNode.Name == Constants.DISPLAY_ELEMENT) && (jAttribute.Name == Constants.DISPLAY_TYPE_ATTRIBUTE))
                                {
                                    sensor.DisplayType = jAttribute.Value;
                                }
                                else if ((jNode.Name == Constants.DISPLAY_ELEMENT) && (jAttribute.Name == Constants.DISPLAY_X))
                                {
                                    sensor.DisplayX = jAttribute.Value;
                                }
                                else if ((jNode.Name == Constants.DISPLAY_ELEMENT) && (jAttribute.Name == Constants.DISPLAY_Y))
                                {
                                    sensor.DisplayY = jAttribute.Value;
                                }
                                else if ((jNode.Name == Constants.CALIBRATION_ELEMENT) && (jAttribute.Name == Constants.XMEAN_ATTRIBUTE))
                                {
                                    sensor.XMean = Convert.ToDouble(jAttribute.Value);
                                }
                                else if ((jNode.Name == Constants.CALIBRATION_ELEMENT) && (jAttribute.Name == Constants.XSTD_ATTRIBUTE))
                                {
                                    sensor.XStd = Convert.ToDouble(jAttribute.Value);
                                }
                                else if ((jNode.Name == Constants.CALIBRATION_ELEMENT) && (jAttribute.Name == Constants.YMEAN_ATTRIBUTE))
                                {
                                    sensor.YMean = Convert.ToDouble(jAttribute.Value);
                                }
                                else if ((jNode.Name == Constants.CALIBRATION_ELEMENT) && (jAttribute.Name == Constants.YSTD_ATTRIBUTE))
                                {
                                    sensor.YStd = Convert.ToDouble(jAttribute.Value);
                                }
                                else if ((jNode.Name == Constants.CALIBRATION_ELEMENT) && (jAttribute.Name == Constants.ZMEAN_ATTRIBUTE))
                                {
                                    sensor.ZMean = Convert.ToDouble(jAttribute.Value);
                                }
                                else if ((jNode.Name == Constants.CALIBRATION_ELEMENT) && (jAttribute.Name == Constants.ZSTD_ATTRIBUTE))
                                {
                                    sensor.ZStd = Convert.ToDouble(jAttribute.Value);
                                }


                                //display element has children
                                if (jNode.Name == Constants.DISPLAY_ELEMENT)
                                {

                                    foreach (XmlNode kNode in jNode.ChildNodes)
                                    {
                                        foreach (XmlAttribute kAttribute in kNode.Attributes)
                                        {
                                            if ((kNode.Name == Constants.COLOR_ELEMENT) && (kAttribute.Name == Constants.ON_ATTRIBUTE))
                                            {
                                                sensor.ColorOn = kAttribute.Value;
                                            }
                                            else if ((kNode.Name == Constants.COLOR_ELEMENT) && (kAttribute.Name == Constants.OFF_ATTRIBUTE))
                                            {
                                                sensor.ColorOff = kAttribute.Value;
                                            }
                                        }
                                    }
                                }
                            }



                        }

                        //if (sensor.SensorClass.ToLower()==Constants.MITES.ToLower())
                        //{
                        if (sensor.SensorClass == Constants.BUILTIN)
                        {
                            annotation.HasBuiltinSensors = true;
                            annotation.TotalBuiltInSensors = annotation.TotalBuiltInSensors + 1;
                        }
                        annotation.Sensors.Add(sensor);
                        sensor.Index = annotation.Sensors.IndexOf(sensor);
                        annotation.SensorsIndex.Add(Convert.ToInt32(sensor.ID), sensor.Index);
                        //}
                        // else if (sensor.SensorClass.ToLower()== Constants.BUILTIN.ToLower())
                        //{
                        //    annotation.HasBuiltinSensors = true;
                        //   annotation.BuiltinSensors.Add(sensor);
                        // }
                    }
                    //parsing file information
                    else if (iNode.Name == Constants.SENSORS_ELEMENT)
                    {
                        foreach (XmlNode rNode in iNode.ChildNodes)
                        {


                            if (rNode.Name == Constants.SENSOR_ELEMENT)
                            {
                                Sensor sensor = new Sensor();

                                foreach (XmlAttribute iAttribute in rNode.Attributes)
                                {
                                    //read nodes attributes
                                    if (iAttribute.Name == Constants.CLASS_ATTRIBUTE)
                                    {
                                        sensor.SensorClass = iAttribute.Value;
                                    }
                                    else if (iAttribute.Name == Constants.TYPE_ATTRIBUTE)
                                    {
                                        sensor.Type = iAttribute.Value;
                                    }
                                }


                                foreach (XmlNode jNode in rNode.ChildNodes)
                                {
                                    //Console.WriteLine(jNode.Name);

                                    foreach (XmlAttribute jAttribute in jNode.Attributes)
                                    {
                                        //read nodes attributes
                                        if ((jNode.Name == Constants.ID_ELEMENT) && (jAttribute.Name == Constants.ID_ATTRIBUTE))
                                        {
                                            sensor.ID = jAttribute.Value;

                                            //if this is an HR sensor
                                            if (Convert.ToInt32(jAttribute.Value) == 0)
                                            {
                                                annotation.IsHR = true;
                                            }
                                            if ((firstAccel == false) && (Convert.ToInt32(jAttribute.Value) > 0))
                                            {
                                                annotation.FirstAccelerometer = Convert.ToInt32(jAttribute.Value);
                                                firstAccel = true;
                                            }

                                            if (annotation.MaximumSensorID < Convert.ToInt32(jAttribute.Value))
                                                annotation.MaximumSensorID = Convert.ToInt32(jAttribute.Value);

                                        }
                                        else if ((jNode.Name == Constants.OBJECT_ELEMENT) && (jAttribute.Name == Constants.TEXT_ATTRIBUTE))
                                        {
                                            sensor.SensorObject = jAttribute.Value;
                                        }
                                        else if ((jNode.Name == Constants.RECEIVER_ELEMENT) && (jAttribute.Name == Constants.ID_ATTRIBUTE))
                                        {
                                            int receiver_id = Convert.ToInt32(jAttribute.Value);
                                            if ((receiver_id < maxReceivers) && (receiver_id >= 0))
                                            {
                                                annotation.NumberSensors[receiver_id] = annotation.NumberSensors[receiver_id] + 1;
                                                sensor.Receiver = jAttribute.Value;
                                                //if (countedReceiver[receiver_id] == false)
                                                //{
                                                //  annotation.TotalReceivers++;
                                                // countedReceiver[receiver_id] = true;
                                                // }
                                            }
                                            else
                                                throw new Exception("Receiver in sensor file out of bound");

                                            //sensor.Receiver = jAttribute.Value;                                                                        
                                            //if (Convert.ToInt32(sensor.Receiver) == 1)
                                            //{
                                            //    annotation.SensorCount1++;
                                            //}
                                            //else if (Convert.ToInt32(sensor.Receiver) == 2)
                                            //{
                                            //    annotation.SensorCount2++;
                                            //}
                                        }
                                        else if ((jNode.Name == Constants.LOCATION_ELEMENT) && (jAttribute.Name == Constants.TEXT_ATTRIBUTE))
                                        {
                                            sensor.Location = jAttribute.Value;
                                        }
                                        else if ((jNode.Name == Constants.DESCRIPTION_ELEMENT) && (jAttribute.Name == Constants.TEXT_ATTRIBUTE))
                                        {
                                            sensor.Description = jAttribute.Value;
                                        }
                                        else if ((jNode.Name == Constants.DESCRIPTION_ELEMENT) && (jAttribute.Name == Constants.SR_ATTRIBUTE))
                                        {
                                            sensor.SamplingRate = Convert.ToInt32(jAttribute.Value); //TODO
                                        }
                                        else if ((jNode.Name == Constants.DISPLAY_ELEMENT) && (jAttribute.Name == Constants.DISPLAY_TYPE_ATTRIBUTE))
                                        {
                                            sensor.DisplayType = jAttribute.Value;
                                        }
                                        else if ((jNode.Name == Constants.DISPLAY_ELEMENT) && (jAttribute.Name == Constants.DISPLAY_X))
                                        {
                                            sensor.DisplayX = jAttribute.Value;
                                        }
                                        else if ((jNode.Name == Constants.DISPLAY_ELEMENT) && (jAttribute.Name == Constants.DISPLAY_Y))
                                        {
                                            sensor.DisplayY = jAttribute.Value;
                                        }
                                        else if ((jNode.Name == Constants.CALIBRATION_ELEMENT) && (jAttribute.Name == Constants.XMEAN_ATTRIBUTE))
                                        {
                                            sensor.XMean = Convert.ToDouble(jAttribute.Value);
                                        }
                                        else if ((jNode.Name == Constants.CALIBRATION_ELEMENT) && (jAttribute.Name == Constants.XSTD_ATTRIBUTE))
                                        {
                                            sensor.XStd = Convert.ToDouble(jAttribute.Value);
                                        }
                                        else if ((jNode.Name == Constants.CALIBRATION_ELEMENT) && (jAttribute.Name == Constants.YMEAN_ATTRIBUTE))
                                        {
                                            sensor.YMean = Convert.ToDouble(jAttribute.Value);
                                        }
                                        else if ((jNode.Name == Constants.CALIBRATION_ELEMENT) && (jAttribute.Name == Constants.YSTD_ATTRIBUTE))
                                        {
                                            sensor.YStd = Convert.ToDouble(jAttribute.Value);
                                        }
                                        else if ((jNode.Name == Constants.CALIBRATION_ELEMENT) && (jAttribute.Name == Constants.ZMEAN_ATTRIBUTE))
                                        {
                                            sensor.ZMean = Convert.ToDouble(jAttribute.Value);
                                        }
                                        else if ((jNode.Name == Constants.CALIBRATION_ELEMENT) && (jAttribute.Name == Constants.ZSTD_ATTRIBUTE))
                                        {
                                            sensor.ZStd = Convert.ToDouble(jAttribute.Value);
                                        }


                                        //display element has children
                                        if (jNode.Name == Constants.DISPLAY_ELEMENT)
                                        {

                                            foreach (XmlNode kNode in jNode.ChildNodes)
                                            {
                                                foreach (XmlAttribute kAttribute in kNode.Attributes)
                                                {
                                                    if ((kNode.Name == Constants.COLOR_ELEMENT) && (kAttribute.Name == Constants.ON_ATTRIBUTE))
                                                    {
                                                        sensor.ColorOn = kAttribute.Value;
                                                    }
                                                    else if ((kNode.Name == Constants.COLOR_ELEMENT) && (kAttribute.Name == Constants.OFF_ATTRIBUTE))
                                                    {
                                                        sensor.ColorOff = kAttribute.Value;
                                                    }
                                                }
                                            }
                                        }
                                    }



                                }

                                //if (sensor.SensorClass.ToLower()==Constants.MITES.ToLower())
                                //{
                                if (sensor.SensorClass == Constants.BUILTIN)
                                {
                                    annotation.HasBuiltinSensors = true;
                                    annotation.TotalBuiltInSensors = annotation.TotalBuiltInSensors + 1;
                                }
                                annotation.Sensors.Add(sensor);
                                sensor.Index = annotation.Sensors.IndexOf(sensor);
                                annotation.SensorsIndex.Add(Convert.ToInt32(sensor.ID), sensor.Index);
                                //}
                                // else if (sensor.SensorClass.ToLower()== Constants.BUILTIN.ToLower())
                                //{
                                //    annotation.HasBuiltinSensors = true;
                                //   annotation.BuiltinSensors.Add(sensor);
                                // }
                            }
                        }
                    }

                                                      
                }
            }

            return annotation;
        }

        public bool validate()
        {

            XmlSchemaSet sc = new XmlSchemaSet();
            // Add the schema to the collection.

            sc.Add("urn:mites-schema", this.xsdFile);
            // Set the validation settings.    
            XmlReaderSettings settings = new XmlReaderSettings();
            settings.ValidationType = ValidationType.Schema;
            settings.Schemas = sc;
            settings.ValidationEventHandler += new ValidationEventHandler(ValidationCallBack);
            // Create the XmlReader object.
            XmlReader reader = XmlReader.Create(this.xmlFile, settings);
            // Parse the file. 
            while (reader.Read())
            {
                ;
            }
            return true;

        }

        private void ValidationCallBack(object sender, ValidationEventArgs e)
        {
            throw new Exception(e.Message);
        }

    }
}
