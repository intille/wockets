using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using System.Xml.Schema;
using System.Collections;

namespace SXML
{
    public class ConfigurationReader
    {
        public const string DEFAULT_XML_FILE = "SensorConfigurations.xml";
        public const string DEFAULT_XSD_FILE = "SensorConfigurations.xsd";

        private string xmlFile;
        private string xsdFile;

        public ConfigurationReader(string dataDirectory)
        {
            this.xmlFile = dataDirectory+DEFAULT_XML_FILE;
            this.xsdFile = dataDirectory + DEFAULT_XSD_FILE;
        }

        public Configurations parse()
        {
            Configurations configurations = new Configurations();

      
            XmlDocument dom = new XmlDocument();
            dom.Load(this.xmlFile);
            XmlNode xNode = dom.DocumentElement;

            if ((xNode.Name == Constants.CONFIGURATIONS_ELEMENT) && (xNode.HasChildNodes))
            {
                //Sensorset nodes
                foreach (XmlNode iNode in xNode.ChildNodes)
                {
                    
                    if (iNode.Name == Constants.SENSORSET_ELEMENT)
                    {
                        Configuration configuration = new Configuration();

                        foreach (XmlNode jNode in iNode.ChildNodes)
                        {
                            if (jNode.Name == Constants.NAME_ELEMENT)
                            {
                                configuration.Name = jNode.InnerXml;
                                if (jNode.InnerXml.Length > configurations.LongestLabel.Length)
                                {
                                    configurations.LongestLabel = jNode.InnerXml;
                                }
                            }
                            else if (jNode.Name == Constants.DESCRIPTION_ELEMENT)
                            {
                                configuration.Description = jNode.InnerXml;

                                if (jNode.InnerXml.Length > configurations.LongestDescription.Length)
                                {
                                    configurations.LongestDescription = jNode.InnerXml;
                                }
                            }
                            else if (jNode.Name == Constants.FILE_ELEMENT)
                            {
                                configuration.FileName = jNode.InnerXml;
                            }
                            
                        }

                        configurations.SensorConfigurations.Add(configuration);
                    }
                }
            }
            return configurations;                            
        }

#if (!PocketPC)
        public bool validate()
        {

            try
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
            catch (Exception e)
            {
                throw new Exception("Error in (SXML.ConfigurationReader,validate):" + e.ToString());
            }

        }

        private void ValidationCallBack(object sender, ValidationEventArgs e)
        {
            throw new Exception(e.Message);
        }
#endif
    }
}
