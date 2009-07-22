using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using Wockets.Utils;


namespace Wockets.Data.Annotation
{
    public class Session: XMLSerializable
    {
        private const string ANNOTATION_ELEMENT="ANNOTATION";
        private const string FILEINFO_ELEMENT = "FILEINFO";
        private const string SUBJECT_ELEMENT="SUBJECT";
        private const string LOCATION_ELEMENT="LOCATION";
        private const string OBSERVER_ELEMENT="OBSERVER";
        private const string NOTES_ELEMENT="NOTES";
        private const string NAME_ATTRIBUTE = "NAME";

        private const string ENDDATE_ATTRIBUTE = "ENDDATE";
        private const string STARTTIME_ATTRIBUTE = "STARTTIME";
        private const string ENDTIME_ATTRIBUTE = "ENDTIME";
        private const string COLOR_ATTRIBUTE = "COLOR";

        private string subject;
        private string location;
        private string observer;
        private string notes;
        private ConcurrentActivityLists activityLists;
        private AnnotationList annotations;

        public Session()
        {
            this.activityLists = new ConcurrentActivityLists();
            this.annotations = new AnnotationList();
        }

        #region Access Properties
        public string _Subject
        {
            get
            {
                return this.subject;
            }
            set
            {
                this.subject = value;
            }
        }

        public string _Location
        {
            get
            {
                return this.location;
            }

            set
            {
                this.location = value;
            }
        }

        public string _Observer
        {
            get
            {
                return this.observer;
            }

            set
            {
                this.observer = value;
            }
        }

        public string _Notes
        {
            get
            {
                return this.notes;
            }
            set
            {
                this.notes = value;
            }
        }

        public ConcurrentActivityLists OverlappingActivityLists
        {
            get
            {
                return this.activityLists;
            }
        }

        public AnnotationList Annotations
        {
            get
            {
                return this.annotations;
            }
        }
        #endregion Access Properties

        public string ToXML()
        {
            string xml = "";
            xml += "<?xml version='1.0'?>\n";
            xml += "<" + ANNOTATION_ELEMENT + " xmlns=\"urn:mites-schema\">\n";
            xml += "<" + FILEINFO_ELEMENT + ">\n";
            xml += "<" + SUBJECT_ELEMENT + " " + NAME_ATTRIBUTE + "=\"" + this.subject + "\" />\n";
            xml += "<" + LOCATION_ELEMENT + " " + NAME_ATTRIBUTE + "=\"" + this.location + "\" />\n";
            xml += "<" + OBSERVER_ELEMENT + " " + NAME_ATTRIBUTE + "=\"" + this.observer + "\" />\n";
            xml += "<" + NOTES_ELEMENT + " " + NAME_ATTRIBUTE + "=\"" + this.notes + "\" />\n";
            xml += "</" + FILEINFO_ELEMENT + ">\n";
            xml += this.activityLists.ToXML();
            xml += this.annotations.ToXML();
            xml += "</" + ANNOTATION_ELEMENT + ">\n";
            return xml;
        }

        public string ToCSV()
        {
            string csv = "";

            csv += STARTTIME_ATTRIBUTE + "," + ENDTIME_ATTRIBUTE + "," + COLOR_ATTRIBUTE;
            csv += this.OverlappingActivityLists.ToCSV();
            csv += "\n";
            csv += this.annotations.ToCSV();
            return csv;
        }
        public void FromXML(string xml)
        {
            XmlDocument dom = new XmlDocument();
            dom.Load(xml);
            XmlNode xNode = dom.DocumentElement;

            if ((xNode.Name == ANNOTATION_ELEMENT) && (xNode.HasChildNodes))
            {
                foreach (XmlNode iNode in xNode.ChildNodes)
                {
                    if (iNode.Name == ConcurrentActivityLists.ConcurrentActivityList_ELEMENT)
                        this.activityLists.FromXML(iNode.OuterXml);
                    else if (iNode.Name == AnnotationList.ANNOTATIONLIST_ELEMENT)
                        this.annotations.FromXML(iNode.OuterXml);
                    else if (iNode.Name == FILEINFO_ELEMENT)
                    {
                        foreach (XmlNode jNode in iNode.ChildNodes)
                        {
                            foreach (XmlAttribute jAttribute in jNode.Attributes)
                            {
                                if (jAttribute.Name == NAME_ATTRIBUTE)
                                {
                                    if (jNode.Name == SUBJECT_ELEMENT)
                                        this.subject = jAttribute.Value;
                                    else if (jNode.Name == OBSERVER_ELEMENT)
                                        this.observer = jAttribute.Value;
                                    else if (jNode.Name == LOCATION_ELEMENT)
                                        this.location = jAttribute.Value;
                                    else if (jNode.Name == NOTES_ELEMENT)
                                        this.notes = jAttribute.Value;
                                }
                            }
                        }
                    }
                }

            }
        }
    }
}
