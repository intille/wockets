using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Utils
{
    public class CircularBuffer
    {
        public byte[] _Bytes;
        public double[] _Timestamp;
        public int _Head;
        public int _Tail;

        public CircularBuffer(int size)
        {
            this._Bytes = new byte[size];
            this._Timestamp = new double[size];
            this._Head = 0;
            this._Tail = 0;
        }

    
    }
}
