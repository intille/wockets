using System;
using System.Collections.Generic;
using System.Xml;
using Wockets.Utils;

namespace Wockets
{

    public sealed class WocketsControllerList : List<WocketsController>, XMLSerializable
    {
        #region Serialization Constants
        private const string WOCKETSCONTROLLERS_FILE = "WocketsControllers.xml";
        private const string WOCKETSCONTROLLERS_ELEMENT = "WOCKETSCONTROLLERS";
        private const string WOCKETCONTROLLER_ELEMENT = "WOCKETCONTROLLER";
        private const string DESCRIPTION_ELEMENT = "DESCRIPTION";
        private const string NAME_ELEMENT = "NAME";
        private const string FILE_ELEMENT = "CONFIGURATIONFILE";
        #endregion Serialization Constants

        public WocketsControllerList()
        {
        }

        public string ToXML()
        {
            string xml = "<" + WOCKETSCONTROLLERS_ELEMENT + ">\n";
            foreach (WocketsController controller in this)
            {
                xml += "<" + WOCKETCONTROLLER_ELEMENT + ">\n";
                xml += "<" + NAME_ELEMENT + ">" + controller._Name + "<" + NAME_ELEMENT + ">\n";
                xml += "<" + DESCRIPTION_ELEMENT + ">" + controller._Description + "<" + DESCRIPTION_ELEMENT + ">\n";
                xml += "<" + FILE_ELEMENT + ">" + controller._FileName+ "<" + FILE_ELEMENT + ">\n";
                xml += "</" + WOCKETCONTROLLER_ELEMENT + ">\n";

            }
            xml += "</" + WOCKETSCONTROLLERS_ELEMENT + ">\n";
            return xml;
        }

        public void FromXML(string xmlFile)
        {
            int wocketsIndex=0;
            XmlDocument dom = new XmlDocument();
            dom.Load(xmlFile + WOCKETSCONTROLLERS_FILE);
            XmlNode xNode = dom.DocumentElement;

            if ((xNode.Name == WOCKETSCONTROLLERS_ELEMENT) && (xNode.HasChildNodes))
            {
                foreach (XmlNode jNode in xNode.ChildNodes)
                {
                    if (jNode.Name == WOCKETCONTROLLER_ELEMENT)
                    {
                        string name="";
                        string description="";
                        string filename="";
                        foreach (XmlNode kNode in jNode.ChildNodes)
                        {                            
                             if (kNode.Name == NAME_ELEMENT)
                                 name= kNode.InnerXml;
                             else if (kNode.Name == DESCRIPTION_ELEMENT)
                                 description= kNode.InnerXml;
                             else if (kNode.Name == FILE_ELEMENT)
                                 filename= kNode.InnerXml;                                      
                        }
                        this.Insert(wocketsIndex++, new WocketsController(name, filename, description));
                    }
                }
            }
        }
    }
}
