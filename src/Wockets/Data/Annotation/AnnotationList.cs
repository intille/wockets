using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using Wockets.Utils;

namespace Wockets.Data.Annotation
{
    public class AnnotationList : List<Annotation>, XMLSerializable
    {
        public const string ANNOTATIONLIST_ELEMENT = "DATA";

        public AnnotationList()
        {
        }
        public string ToXML()
        {
            string xml = "";
            xml += "<" + ANNOTATIONLIST_ELEMENT + ">\n";
            for (int i=0;(i<this.Count);i++)
                xml += this[i].ToXML();           
            xml += "</" + ANNOTATIONLIST_ELEMENT + ">\n";
            return xml;
        }

        public string ToCSV()
        {
            string csv = "";
            for (int i = 0; (i < this.Count); i++)
                csv += this[i].ToCSV()+"\n";           
            return csv;
        }
        public void FromXML(string xml)
        {
            XmlDocument dom = new XmlDocument();
            dom.LoadXml(xml);
            XmlNode iNode = dom.DocumentElement;
            int index = 0;
            if (iNode.Name == ANNOTATIONLIST_ELEMENT)            
                foreach (XmlNode jNode in iNode.ChildNodes)
                    if (jNode.Name == Annotation.ANNOTATION_ELEMENT)
                    {
                        Annotation annotation = new Annotation();
                        annotation.FromXML(jNode.OuterXml);
                        this.Insert(index++, annotation);
                    }
        }

    }
}
