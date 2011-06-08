using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using Wockets.Utils;

namespace Wockets.Data.Annotation
{
    public class AnnotationProtocol: XMLSerializable
    {
        public const string PROTOCOL_ELEMENT = "PROTOCOL";
        public const string NAME_ELEMENT = "NAME";
        public const string DESCRIPTION_ELEMENT = "DESCRIPTION";
        public const string FILE_ELEMENT = "FILE";

        private string name;
        private string description;
        private string fileName;

        public AnnotationProtocol()
        {
            this.name = "";
            this.description = "";
            this.fileName = "";
        }

        #region Access Properties
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

        public string _FileName
        {
            get
            {
                return this.fileName;
            }

            set
            {
                this.fileName = value;
            }
        }
        #endregion Access Properties

        public string ToXML()
        {
            string xml = "";
            return xml;
        }
        public void FromXML(string xml)
        {
            XmlDocument dom = new XmlDocument();
            dom.LoadXml(xml);
            XmlNode iNode = dom.DocumentElement;
            if (iNode.Name == PROTOCOL_ELEMENT)
            {
                foreach (XmlNode jNode in iNode.ChildNodes)
                {
                    if (jNode.Name == NAME_ELEMENT)                    
                        this.name = jNode.InnerXml;                    
                    else if (jNode.Name == DESCRIPTION_ELEMENT)
                        this.description= jNode.InnerXml;                    
                    else if (jNode.Name == FILE_ELEMENT)
                        this.fileName = jNode.InnerXml;                    
                }    
            }
        }
    }
}
