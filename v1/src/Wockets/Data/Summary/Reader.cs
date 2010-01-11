using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using System.Xml.Schema;

namespace Wockets.Data.Summary
{
    public class Reader
    {
        public const string DEFAULT_XML_FILE = "ActivitySummary.xml";
        private string xmlFile;
        private string xsdFile;

        public Reader(string masterDirectory, string dataDirectory)//, System.Windows.Forms.Form caller)
        {
            this.xmlFile = dataDirectory + "\\" + DEFAULT_XML_FILE;      
        }

        public ActivityListSummary parse()
        {
            ActivityListSummary activityList = new ActivityListSummary();
            XmlDocument dom = new XmlDocument();
            dom.Load(this.xmlFile);
            XmlNode xNode = dom.DocumentElement;
            if ((xNode.Name == Constants.ACTIVITIES_SUMMARY_ELEMENT) && (xNode.HasChildNodes))
            {

                foreach (XmlNode iNode in xNode.ChildNodes)
                {
                    //Console.WriteLine(iNode.Name);

                    //parsing file information
                    if (iNode.Name == Constants.ACTIVITY_ELEMENT)
                    {
                        ActivitySummary a = new ActivitySummary();
                        foreach (XmlNode jNode in iNode.ChildNodes)
                        {
                            //Console.WriteLine(jNode.Name);

                            foreach (XmlAttribute jAttribute in jNode.Attributes)
                            {
                                if (jAttribute.Name == Constants.NAME_ATTRIBUTE)
                                    a.Name = jAttribute.Value;
                                else if (jAttribute.Name == Constants.START_TIME_ATTRIBUTE)
                                    a.StartTime = Convert.ToDouble(jAttribute.Value);
                                else if (jAttribute.Name == Constants.END_TIME_ATTRIBUTE)
                                    a.EndTime = Convert.ToDouble(jAttribute.Value);
                                else if (jAttribute.Name == Constants.VALUE_ATTRIBUTE)
                                    a.Percent =  Convert.ToInt32(jAttribute.Value);
                            }

                        }

                        activityList.Activities.Add(a);
                    }
                }
            }

            return activityList;
        }
    }
}
