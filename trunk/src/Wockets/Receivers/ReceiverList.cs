using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using Wockets.Utils;

namespace Wockets.Receivers
{
    public sealed class ReceiverList : List<Receiver>, XMLSerializable
    {
        #region Serialization Constants
        public const string RECEIVERS_ELEMENT = "RECEIVERS";
        private const string TYPE_ATTRIBUTE = "type";
        #endregion Serialization Constants

        public ReceiverList()
        {
        }
        public string ToXML()
        {
            string xml = "<" + RECEIVERS_ELEMENT + ">\n";
            for (int i = 0; (i < this.Count); i++)
                xml += this[i].ToXML();
            xml += "</" + RECEIVERS_ELEMENT + ">\n";
            return xml;
        }

        public void FromXML(string xml)
        {
            XmlDocument dom = new XmlDocument();
            dom.LoadXml(xml);
            XmlNode xNode = dom.DocumentElement;

            if ((xNode.Name == RECEIVERS_ELEMENT) && (xNode.HasChildNodes))
            {
                foreach (XmlNode jNode in xNode.ChildNodes)
                {
                    if (jNode.Name == Receiver.RECEIVER_ELEMENT)
                    {
                        ReceiverTypes receiverType = ReceiverTypes.Unknown;
                        foreach (XmlAttribute jAttribute in jNode.Attributes)
                        {
                            if (jAttribute.Name == TYPE_ATTRIBUTE)
                                receiverType = (ReceiverTypes)Enum.Parse(typeof(ReceiverTypes), jAttribute.Value, true);
                        }
                        Receiver receiver = null;
#if (PocketPC)
                        if (receiverType == ReceiverTypes.HTCDiamond)
                            receiver = new HTCDiamondReceiver();
                        else 
#endif                        
                        if (receiverType == ReceiverTypes.RFCOMM)
                            receiver = new RFCOMMReceiver();
                        else if (receiverType == ReceiverTypes.StandardCOM)
                            receiver = new StandardCOMReceiver();
                        else if (receiverType == ReceiverTypes.HTCDiamond)
                            receiver = new HTCDiamondReceiver();              
                        receiver.FromXML(jNode.OuterXml);
                        this.Insert(receiver._ID,receiver);

                    }
                }
            }
        }
    }
}
