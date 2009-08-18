using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Utils
{
    public class CircularBuffer
    {
        private byte[] bytes;
        private int head;
        private int tail;

        public CircularBuffer(int size)
        {
            this.bytes = new byte[size];
            this.head = 0;
            this.tail = 0;
        }

        public byte[] _Bytes
        {
            get
            {
                return this.bytes;
            }
            set
            {
                this.bytes = value;
            }
        }

        public int _Head
        {
            get
            {
                return this.head;
            }
            set
            {
                this.head = value;
            }
        }

        public int _Tail
        {
            get
            {
                return this.tail;
            }
            set
            {
                this.tail = value;
            }
        }
    }
}
