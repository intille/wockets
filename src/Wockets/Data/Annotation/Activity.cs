using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using Wockets.Utils;

namespace Wockets.Data.Annotation
{
    public class Activity : XMLSerializable
    {
        public const string ACTIVITY_ELEMENT = "LABEL";
        private const string NAME_ATTRIBUTE = "NAME";
        private string name;
        private string category;

        public Activity(string name, string category)
        {
            this.name = name;
            this.category = category;
        }
        public Activity()
        {
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

        public string _Category
        {
            get
            {
                return this.category;
            }
            set
            {
                this.category = value;
            }
        }
        #endregion Access Properties

        public string ToXML()
        {
            string xml = "";
            xml += "<" + ACTIVITY_ELEMENT + " " + NAME_ATTRIBUTE + "=\"" + this.name + "\" />\n";
            return xml;
        }

     
        public void FromXML(string xml)
        {
                     
            XmlDocument dom = new XmlDocument();
            dom.LoadXml(xml);
            XmlNode iNode = dom.DocumentElement;
            int index = 0;
            if (iNode.Name == ACTIVITY_ELEMENT)
            {
                foreach (XmlAttribute iAttribute in iNode.Attributes)                
                    if (iAttribute.Name == NAME_ATTRIBUTE)
                        this.name = iAttribute.Value.Replace("A - ", "").Replace("A- ", "").Replace(' ', '-').Replace(',', '_').ToLower();                
            }
        }
    }
}
