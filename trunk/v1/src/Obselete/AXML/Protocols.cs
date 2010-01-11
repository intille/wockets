using System;
using System.Collections.Generic;
using System.Text;
using System.Collections;

namespace AXML
{
            
    
    public class Protocols
    {        

        private ArrayList activityProtocols;
        private string longest_label;
        private string longest_description;


        public Protocols()
        {
            this.activityProtocols = new ArrayList();
            this.longest_label = "";
            this.longest_description = "";
        }

        public ArrayList ActivityProtocols
        {
            get
            {
                return this.activityProtocols;
            }
        }


        public string LongestLabel
        {
            get
            {
                return this.longest_label;
            }
            set
            {
                this.longest_label = value;
            }
        }

        public string LongestDescription
        {
            get
            {
                return this.longest_description;
            }
            set
            {
                this.longest_description = value;
            }
        }
        
    }
}
