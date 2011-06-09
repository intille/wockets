using System;
using System.Collections.Generic;
using System.Text;

namespace HousenCS.MITes
{
    public class GenericAccelerometerData
    {

               
        private int channel_id;
        private int type;
        private int x, y, z;
        private int timestamp;
        private double unixtimestamp;
        private int maximumSamplingRate;

        public GenericAccelerometerData(int channel_id)
        {
            this.x = 0;
            this.y = 0;
            this.z = 0;
            this.timestamp = 0;
            this.unixtimestamp = 0;
            this.type = 0;
            this.channel_id = channel_id;
        }

        public int MaximumSamplingRate
        {
            get
            {
                return this.maximumSamplingRate;
            }
            set
            {
                this.maximumSamplingRate = value;
            }
        }
        public int[] toArray()
        {
            int[] data = new int[3];
            data[0] = this.x;
            data[1] = this.y;
            data[2] = this.z;
            return data;
        }

        public byte[] encode6Bytes()
        {
            byte[] b = new byte[6];
            b[0] = (byte)channel_id;
            b[1] = (byte) (x & 0xff);
            b[2] = (byte) (y & 0xff);
            b[3] = (byte) (z & 0xff);
            b[4] = (byte) (((x & 0x0F00) >> 4) | ((y & 0x0F00) >> 8));
            b[5] = (byte) (((z & 0x0F00) >> 4) | (type & 0x0F));
            return b;  
        }

        public void decode6Bytes(byte[] b)
        {
            if (b.Length == 6)
            {
                this.channel_id = (int)(b[0] & 0xFF);
                this.x = (int)( (b[1] & 0xFF) | ( (b[4] & 0xF0) << 4));
                this.y = (int)((b[2] & 0xFF) | ((b[4] & 0x0F) << 8));
                this.z = (int)((b[3] & 0xFF) | ((b[5] & 0xF0) << 4));
                this.type = (int)(b[5] & 0x0F);          
            }
        }
        public int ChannelID
        {
            get
            {
                return this.channel_id;
            }
            set
            {
                this.channel_id = value;
            }
        }

        public int Type
        {
            get
            {
                return this.type;
            }

            set
            {
                this.type = value;
            }
        }
        public int Timestamp
        {
            get
            {
                return this.timestamp;
            }
            set
            {
                this.timestamp = value;
            }
        }

        public double Unixtimestamp
        {
            get
            {
                return this.unixtimestamp;
            }

            set
            {
                this.unixtimestamp = value;
            }
        }


        public int X
        {
            get
            {
                return this.x;
            }
            set
            {
                this.x = value;
            }
        }

        public int Y
        {
            get
            {
                return this.y;
            }
            set
            {
                this.y = value;
            }
        }

        public int Z
        {
            get
            {
                return this.z;
            }
            set
            {
                this.z = value;
            }
        }

        public string toString()
        {
            return this.unixtimestamp + "," + this.x + "," + this.y + "," + this.z;
        }
    
    }
}
