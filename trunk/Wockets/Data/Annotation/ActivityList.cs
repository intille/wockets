using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using Wockets.Utils;

namespace Wockets.Data.Annotation
{
    public class ActivityList : List<Activity>, XMLSerializable
    {
        public const string ACTIVITYLIST_ELEMENT = "CATEGORY";
        private const string NAME_ATTRIBUTE = "NAME";
        private const string PROPERTY_ATTRIBUTE = "PROPERTY";
        private string name;
        private string property;

        public ActivityList()
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

        public string _Property
        {
            get
            {
                return this.property;
            }

            set
            {
                this.property = value;
            }
        }

        #endregion Access Properties

        public string ToXML()
        {
            string xml = "";
            xml += "<" + ACTIVITYLIST_ELEMENT + " " + NAME_ATTRIBUTE + "=\"" + this.name + "\" " + PROPERTY_ATTRIBUTE + "=\"" + this.property + "\">\n";
            for (int i = 0; (i < this.Count); i++)
                xml += this[i].ToXML();
            xml += "</" + ACTIVITYLIST_ELEMENT + ">\n";
            return xml;
        }
        public void FromXML(string xml)
        {
            XmlDocument dom = new XmlDocument();
            dom.LoadXml(xml);
            XmlNode iNode = dom.DocumentElement;
            int index = 0;
            if (iNode.Name == ACTIVITYLIST_ELEMENT)
            {
                foreach (XmlAttribute iAttribute in iNode.Attributes)
                {
                    if (iAttribute.Name == NAME_ATTRIBUTE)                    
                        this.name = iAttribute.Value.Replace("A - ", "").Replace("A- ", "").Replace(' ', '-').Replace(',', '_').ToLower();                    
                    else if (iAttribute.Name == PROPERTY_ATTRIBUTE)                    
                        this.property = iAttribute.Value;                    
                }

                foreach (XmlNode jNode in iNode.ChildNodes)
                    if (jNode.Name == Activity.ACTIVITY_ELEMENT)
                    {
                        Activity activity=new Activity();
                        activity.FromXML(jNode.OuterXml);
                        this.Insert(index++,activity);
                    }
            }
        }
    }
}
