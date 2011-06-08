 using System;
using System.Collections.Generic;
using System.Text;
using System.Collections;

namespace AXML
{
    public class Category
    {
        private string name;
        private string property;
        private ArrayList labels;

        public Category()
        {
            this.labels = new ArrayList();
        }

        public Category(string name, string property)
        {
            this.name=name;
            this.property = property;
            this.labels = new ArrayList();
        }

        public string Name
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

        public string Property
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

        public ArrayList Labels
        {
            get
            {
                return this.labels;
            }
        }

        public string ToXML()
        {
            string xml = "";

            xml += "<" + Constants.CATEGORY_ELEMENT + " "+Constants.NAME_ATTRIBUTE+"=\""+this.name+"\" "+Constants.PROPERTY_ATTRIBUTE+"=\""+this.property+"\">\n";
            foreach (Label label in this.labels)
            {
                xml+=label.ToXML();
            }
            xml += "</" + Constants.CATEGORY_ELEMENT + ">\n";

            return xml;
        }

    }
}
