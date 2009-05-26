using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using Wockets.Utils;

namespace Wockets.Data.Annotation
{
    public class ConcurrentActivityLists : List<ActivityList>, XMLSerializable
    {
        public const string ConcurrentActivityList_ELEMENT = "LABELS";

        public ConcurrentActivityLists()
        {
        }

        public string ToXML()
        {
            string xml = "";
            xml += "<" + ConcurrentActivityList_ELEMENT + ">\n";
            for (int i = 0; (i < this.Count); i++)
                xml += this[i].ToXML();
            xml += "</" + ConcurrentActivityList_ELEMENT + ">\n";
            return xml;
        }
        public void FromXML(string xml)
        {
            XmlDocument dom = new XmlDocument();
            dom.LoadXml(xml);
            XmlNode iNode = dom.DocumentElement;
            int index = 0;
            if (iNode.Name == ConcurrentActivityList_ELEMENT)
                foreach (XmlNode jNode in iNode.ChildNodes)
                    if (jNode.Name == ActivityList.ACTIVITYLIST_ELEMENT)
                    {
                        ActivityList activityList=new ActivityList();
                        activityList.FromXML(jNode.OuterXml);
                        this.Insert(index++, activityList);
                    }
        }
    }
}
