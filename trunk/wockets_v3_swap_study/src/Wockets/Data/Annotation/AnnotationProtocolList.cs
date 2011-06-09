using System;
using System.Collections.Generic;
using System.Xml;
using System.Text;
using Wockets.Utils;

namespace Wockets.Data.Annotation
{
    public class AnnotationProtocolList: List<AnnotationProtocol>, XMLSerializable
    {
        public const string PROTOCOLS_ELEMENT = "PROTOCOLS";

        public AnnotationProtocolList()
        {
           
        }

        public string ToXML()
        {
            string xml = "<"+PROTOCOLS_ELEMENT+">\n";
            for (int i = 0; (i < this.Count); i++)
            {
                xml += this[i].ToXML();
            }
            xml += "</" + PROTOCOLS_ELEMENT + ">\n";
            return xml;
        }
        public void FromXML(string xmlFile)
        {
            XmlDocument dom = new XmlDocument();
            dom.Load(xmlFile);
            XmlNode xNode = dom.DocumentElement;
            int index = 0;
            if ((xNode.Name == PROTOCOLS_ELEMENT) && (xNode.HasChildNodes))
                foreach (XmlNode iNode in xNode.ChildNodes)
                {
                    AnnotationProtocol annotationProtocol=new AnnotationProtocol();
                    annotationProtocol.FromXML(iNode.OuterXml);
                    this.Insert(index++, annotationProtocol);
                }
        }
    }
}
