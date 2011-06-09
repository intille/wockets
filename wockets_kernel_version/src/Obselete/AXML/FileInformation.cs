using System;
using System.Collections.Generic;
using System.Text;

namespace AXML
{

    public class FileInformation
    {
        private string subject;
        private string observer;
        private string location;
        private string notes;

        public string Subject
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

        public string Observer
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

        public string Location
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

        public string Notes
        {
            get
            {
                return this.notes;
            }
            set
            {
                this.notes= value;
            }
        }

        public string ToXML()
        {
            string xml = "";
            xml+="<"+Constants.FILE_INFO_ELEMENT+">\n";
            xml+="<"+Constants.SUBJECT_ELEMENT+" "+Constants.NAME_ATTRIBUTE+"=\""+this.subject+"\" />\n";
            xml+="<"+Constants.LOCATION_ELEMENT+" "+Constants.NAME_ATTRIBUTE+"=\""+this.location+"\" />\n";
            xml+="<"+Constants.OBSERVER_ELEMENT+" "+Constants.NAME_ATTRIBUTE+"=\""+this.observer+"\" />\n";
            xml+="<"+Constants.NOTES_ELEMENT+" "+Constants.NAME_ATTRIBUTE+"=\""+this.notes+"\" />\n";
            xml += "</" + Constants.FILE_INFO_ELEMENT + ">\n";
            return xml;
        }
    }
}
