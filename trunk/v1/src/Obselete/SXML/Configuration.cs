using System;
using System.Collections.Generic;
using System.Text;

namespace SXML
{
    public class Configuration
    {
        private string name;
        private string description;
        private string fileName;

        public Configuration()
        {
            this.name = "";
            this.description = "";
            this.fileName = "";
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

        public string Description
        {
            get
            {
                return this.description;
            }
            set
            {
                this.description = value;
            }
        }

        public string FileName
        {
            get
            {
                return this.fileName;
            }

            set
            {
                this.fileName = value;
            }
        }
    }
}
