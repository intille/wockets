using System;
using System.Collections.Generic;
using System.Collections;
using System.Text;
using System.Xml;
using Wockets.Decoders.Accelerometers;
using Wockets.Utils;

namespace Wockets.Decoders
{
    public sealed class DecoderList : List<Decoder>, XMLSerializable
    {
        #region Serialization Constants
        public const string DECODERS_ELEMENT = "DECODERS";
        private const string TYPE_ATTRIBUTE = "type";
        #endregion Serialization Constants

        public DecoderList()
        {
        }

        public string ToXML()
        {
            string xml = "<" + DECODERS_ELEMENT + ">\n";
            for (int i = 0; (i < this.Count); i++)
                xml += this[i].ToXML();
            xml += "</" + DECODERS_ELEMENT + ">\n";
            return xml;
        }

        public void FromXML(string xml)
        {
            XmlDocument dom = new XmlDocument();
            dom.LoadXml(xml);
            XmlNode xNode = dom.DocumentElement;

            if ((xNode.Name == DECODERS_ELEMENT) && (xNode.HasChildNodes))
            {
                foreach (XmlNode jNode in xNode.ChildNodes)
                {
                    if (jNode.Name == Decoder.DECODER_ELEMENT)
                    {
                        DecoderTypes decoderType = DecoderTypes.Unknown;
                        foreach (XmlAttribute jAttribute in jNode.Attributes)
                        {
                            if (jAttribute.Name == TYPE_ATTRIBUTE)
                                decoderType = (DecoderTypes)Enum.Parse(typeof(DecoderTypes), jAttribute.Value, true);
                        }
                        Decoder decoder = null;
#if (PocketPC)
                        if (decoderType == DecoderTypes.HTCDiamondTouch)
                            decoder = new HTCDiamondTouchDecoder();
                        else 
#endif                        
                        if (decoderType == DecoderTypes.MITes)
                            decoder = new MITesDecoder();
                        else if (decoderType == DecoderTypes.Wockets)
                            decoder = new WocketsDecoder();
                        else if (decoderType == DecoderTypes.Sparkfun)
                            decoder = new SparkfunDecoder();

                         decoder.FromXML(jNode.OuterXml);
                         this.Insert(decoder._ID,decoder);

                    }
                }
            }
        }
    }
}
