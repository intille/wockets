using System;
using System.Collections.Generic;
using System.Text;
using System.Collections;
namespace SXML
{
    public class Configurations
    {
        

        private ArrayList sensorConfigurations;
        private string longestLabel;
        private string longestDescription;

        public Configurations()
        {
            this.sensorConfigurations = new ArrayList();
            this.longestLabel = "";
            this.longestDescription = "";
        }

        public ArrayList SensorConfigurations
        {
            get
            {
                return this.sensorConfigurations;
            }
        }

        public string LongestLabel
        {
            get
            {
                return this.longestLabel;
            }
            set
            {
                this.longestLabel = value;
            }
        }

        public string LongestDescription
        {
            get
            {
                return this.longestDescription;
            }
            set
            {
                this.longestDescription = value;
            }
        }
    }
}
