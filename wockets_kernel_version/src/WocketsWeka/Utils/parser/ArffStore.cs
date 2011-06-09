using System;
using System.Collections.Generic;
using System.Text;
using System.Collections;

namespace WocketsWeka.Utils.parser
{
    public class ArffStore
    {
        private string relation;
        private ArrayList features;
        private ArrayList classes;
        private Hashtable data;
        
        public ArffStore()
        {
            this.features = new ArrayList();
            this.classes = new ArrayList();
            this.data = new Hashtable();
        }

        public string Relation
        {
            get
            {
                return this.relation;
            }
            set
            {
                this.relation = value;
            }
        }

        public ArrayList Features
        {
            get
            {
                return this.features;
            }
            set
            {
                this.features = value;
            }
        }

        public ArrayList Classes
        {
            get
            {
                return this.classes;
            }
            set
            {
                this.classes = value;
            }
        }

        public Hashtable Data
        {
            get
            {
                return this.data;
            }
            set
            {
                this.data = value;
            }
        }

        public ArrayList GetSamples(string arffClass)
        {
            return (ArrayList) this.data[arffClass];
        }
    }
}
