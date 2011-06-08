using System;
using System.Collections.Generic;
using System.Text;
using System.IO;
using System.Text.RegularExpressions;
using weka.core;


namespace WocketsWeka.Utils.parser
{
    public class ArffParser
    {
        private string filename;
        private Instances instances;

        public ArffParser(string filename)
        {
            this.filename = filename;
        }

        public ArffStore parse()
        {
            ArffStore arffStore = new ArffStore();
            instances = new Instances(new StreamReader(this.filename));
            
            //foreach (weka.core.Attribute attribute in instances.enumerateAttributes())
             //   arffStore.Features.Add(attribute.name);

            return arffStore;
           
        }
    }
}
