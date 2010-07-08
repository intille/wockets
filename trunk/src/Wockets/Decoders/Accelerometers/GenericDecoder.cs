using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Utils;

namespace Wockets.Decoders.Accelerometers
{

    public sealed class GenericDecoder : Decoder
    {
        public GenericDecoder()
        {
            this.type = DecoderTypes.Unknown;
        }

        public override int Decode(int sourceSensor, byte[] data, int length)
        {
            return 0;
        }
        public override int Decode(int sourceSensor, CircularBuffer  data,int start,int end)
        {
            return 0;
        }
        public override void Load(ByteReader br)
        { }
        #region Serialization Methods
        public override string ToXML()
        {
            return "";
        }

        public override void FromXML(string xml)
        {

        }
        #endregion Serialization Methods
    }
}
