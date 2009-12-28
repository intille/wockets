using System;
using System.Collections.Generic;
using System.Text;

namespace AXML
{
    public class Label
    {
        private string name;
        private string category;
        //private ATones.Generator tone;

        public Label(string name,string category)
        {
            this.name = name;
            this.category = category;
        }

        //public void InitializeTone(int handle,double frequency)
        //{
         //   tone = new ATones.Generator(0.25,frequency,10000);
          //  tone.InitializeSound(handle);
           // tone.CreateBuffer();
        //}

        //public void PlayTone()
        //{
         //   tone.Play();
        //}
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

        public string Category
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

        public string ToXML()
        {
            string xml = "";
            xml+= "<"+Constants.LABEL_ELEMENT+" "+Constants.NAME_ATTRIBUTE+"=\""+this.name+"\" />\n";
            return xml;
        }

        public string ToValueXML()
        {
            string xml = "";
            xml += "<" + Constants.VALUE_ELEMENT + " " + Constants.LABEL_ATTRIBUTE + "=\"" + this.name + "\" " +
                Constants.CATEGORY_ATTRIBUTE + "=\"" + this.category + "\" />\n";
            return xml;
        }

        
    }
}
