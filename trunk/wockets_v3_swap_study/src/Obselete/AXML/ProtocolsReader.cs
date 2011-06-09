using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using System.Xml.Schema;
using System.Collections;

namespace AXML
{
    public class ProtocolsReader
    {

        public const string DEFAULT_XML_FILE = "ActivityProtocols.xml";
        public const string DEFAULT_XSD_FILE = "ActivityProtocols.xsd";

        private string xmlFile;
        private string xsdFile;

        public ProtocolsReader(string dataDirectory)
        {
            this.xmlFile = dataDirectory + DEFAULT_XML_FILE;
            this.xsdFile = dataDirectory + DEFAULT_XSD_FILE;
        }

        public Protocols parse()
        {
            Protocols protocols = new Protocols();
      
            XmlDocument dom = new XmlDocument();
            dom.Load(this.xmlFile);
            XmlNode xNode = dom.DocumentElement;

            if ((xNode.Name == Constants.PROTOCOLS_ELEMENT) && (xNode.HasChildNodes))
            {
                //Protocol Nodes
                foreach (XmlNode iNode in xNode.ChildNodes)
                {
                   
                    if (iNode.Name == Constants.PROTOCOL_ELEMENT)
                    {
                         
                        Protocol protocol = new Protocol();

                        foreach (XmlNode jNode in iNode.ChildNodes)
                        {
                            if (jNode.Name == Constants.NAME_ELEMENT)
                            {
                                protocol.Name = jNode.InnerXml;
                                if (jNode.InnerXml.Length > protocols.LongestLabel.Length)
                                {
                                    protocols.LongestLabel = jNode.InnerXml;
                                }
                            }
                            else if (jNode.Name == Constants.DESCRIPTION_ELEMENT)
                            {
                                protocol.Description = jNode.InnerXml;
                                if (jNode.InnerXml.Length > protocols.LongestDescription.Length)
                                {
                                    protocols.LongestDescription = jNode.InnerXml;
                                }
                            }
                            else if (jNode.Name == Constants.FILE_ELEMENT)
                            {
                                protocol.FileName = jNode.InnerXml;
                            }
                            
                        }

                        protocols.ActivityProtocols.Add(protocol);
                    }
                }

               
            }
            return protocols ;                            
        }

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

    }
}
