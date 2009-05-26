using System;
using System.Collections.Generic;
using System.Text;
using System.IO;
using NLog;

namespace WocketControlLib
{
    public class FeatureStream
    {
        //8 bytes for the write count 
        //8 bytes for the timestamp
        //4 bytes for the version number
        public const int RESERVED_BYTES = 20;
        private int availableBytes;
        private long previousWriteTotal;

        private Stream stream;
        private BinaryReader reader;
        private Feature feature;
        private static Logger logger = LogManager.GetLogger("FeatureStream");
        //private byte[] reusableBuffer = new byte[8];//8 is the largest number of bytes in any data type (doubles and longs)
        public FeatureStream(Stream streamParam, Feature featureParam)
        {
            streamParam.Seek(0, SeekOrigin.Begin);
            byte[] longBytes = new byte[8];
            streamParam.Read(longBytes, 0, longBytes.Length);
            //this is the first long in the stream, which is reserved as a counter.
            //the writer always updates this long when it writes to the stream
            long totalBytesWritten = BitConverter.ToInt64(longBytes, 0);
            //the starting position is the position in the circular buffer
            //consisting of the full stream length except the first 8 bytes
            int offset = (int) (totalBytesWritten % (streamParam.Length - RESERVED_BYTES)) + RESERVED_BYTES;
            streamParam.Seek(offset, SeekOrigin.Begin);
            availableBytes = 0;
            previousWriteTotal = totalBytesWritten;
            stream = streamParam;
            reader = new BinaryReader(stream);
            feature = featureParam;
        }

        internal void updateWriteTotal()
        {
            lock (this)
            {
                long lastPosition = stream.Position;
                stream.Seek(0, SeekOrigin.Begin);
                long newWriteTotal = reader.ReadInt64();
                stream.Seek(lastPosition, SeekOrigin.Begin);
                if (newWriteTotal == previousWriteTotal)
                    return;//should stop here most of the time
                long difference = newWriteTotal - previousWriteTotal;
                availableBytes += (int)difference;
                previousWriteTotal = newWriteTotal;

                //this shouldn't happen.... often
                //it means we've lost some data because the reader isn't going fast enough for the writer
                if (difference > stream.Length)
                {
                    logger.Warn("feature: " + feature + " is being read too slowly, missing data because of the circular buffer");
                    //reset to the furthest back point
                    long position = (newWriteTotal % (stream.Length - RESERVED_BYTES)) + RESERVED_BYTES;
                    stream.Seek(position, SeekOrigin.Begin);
                }
            }
        }
        internal void updateStream(Stream streamParam)
        {
            lock (this)
            {
                long position = stream.Position;
                reader.Close();
                stream.Close();
                stream = streamParam;
                stream.Seek(position, SeekOrigin.Begin);
                reader = new BinaryReader(stream);
            }
        }

        public Feature Feature { get { return feature; } }
        public TimeSpan Period { get { return feature.Period; } }
        public int Available { get { lock (this) return availableBytes; } }

        public int readInts(int[] buffer, int offset, int length)
        {
            lock (this)
            {
                int ii;
                for (ii = 0; ii < length && availableBytes - (ii * sizeof(int)) > 0; ii++)
                {
                    try
                    {
                        buffer[offset + ii] = reader.ReadInt32();
                    }
                    catch (EndOfStreamException) 
                    {
                        stream.Seek(RESERVED_BYTES, SeekOrigin.Begin);
                        ii--;
                    }
                }
                availableBytes -= ii * sizeof(int);
                return ii;
            }
        }
        public int readBytes(byte[] buffer, int offset, int length) 
        {
            lock (this)
            {
                int bytesRead = stream.Read(buffer, offset, length);
                availableBytes -= bytesRead;
                return bytesRead;
            }
        }
        public int readLongs(long[] buffer, int offset, int length)
        {
            lock (this)
            {
                int ii;
                for (ii = 0; ii < length && availableBytes - (ii * sizeof(long)) > 0; ii++)
                {
                    try
                    {
                        buffer[offset + ii] = reader.ReadInt64();
                    }
                    catch (EndOfStreamException)
                    {
                        stream.Seek(RESERVED_BYTES, SeekOrigin.Begin);
                        ii--;
                    }
                }
                availableBytes -= ii * sizeof(long);
                return ii;
            }
        }
        public int readDoubles(double[] buffer, int offset, int length)
        {
            lock (this)
            {
                int ii;
                for (ii = 0; ii < length && availableBytes - (ii * sizeof(double)) > 0; ii++)
                {
                    try
                    {
                        buffer[offset + ii] = reader.ReadDouble();
                    }
                    catch (EndOfStreamException)
                    {
                        stream.Seek(RESERVED_BYTES, SeekOrigin.Begin);
                        ii--;
                    }
                }
                availableBytes -= ii * sizeof(double);
                return ii;
            }
        }
        public int readFlots(float[] buffer, int offset, int length)
        {
            lock (this)
            {
                int ii;
                for (ii = 0; ii < length && availableBytes - (ii * sizeof(float)) > 0; ii++)
                {
                    try
                    {
                        buffer[offset + ii] = reader.ReadSingle();
                    }
                    catch (EndOfStreamException)
                    {
                        stream.Seek(RESERVED_BYTES, SeekOrigin.Begin);
                        ii--;
                    }
                }
                availableBytes -= ii * sizeof(float);
                return ii;
            }
        }
        public int readShorts(short[] buffer, int offset, int length)
        {
            lock (this)
            {
                int ii;
                for (ii = 0; ii < length && availableBytes - (ii * sizeof(short)) > 0; ii++)
                {
                    try
                    {
                        buffer[offset + ii] = reader.ReadInt16();

                    }
                    catch (EndOfStreamException)
                    {
                        stream.Seek(RESERVED_BYTES, SeekOrigin.Begin);
                        ii--;
                    }
                }
                availableBytes -= ii * sizeof(short);
                return ii;
            }
        }
        public int readUInts(uint[] buffer, int offset, int length)
        {
            lock (this)
            {
                int ii;
                for (ii = 0; ii < length && availableBytes - (ii * sizeof(uint)) > 0; ii++)
                {
                    try
                    {
                        buffer[offset + ii] = reader.ReadUInt32();
                    }
                    catch (EndOfStreamException)
                    {
                        stream.Seek(RESERVED_BYTES, SeekOrigin.Begin);
                        ii--;
                    }
                }
                availableBytes -= ii * sizeof(uint);
                return ii;
            }
        }
        public int readUShorts(ushort[] buffer, int offset, int length)
        {
            lock (this)
            {
                int ii;
                for (ii = 0; ii < length && availableBytes - (ii * sizeof(ushort)) > 0; ii++)
                {
                    try
                    {
                        buffer[offset + ii] = reader.ReadUInt16();
                    }
                    catch (EndOfStreamException)
                    {
                        stream.Seek(RESERVED_BYTES, SeekOrigin.Begin);
                        ii--;
                    }
                }
                availableBytes -= ii * sizeof(ushort);
                return ii;
            }
        }
        public int readULongs(ulong[] buffer, int offset, int length)
        {
            lock (this)
            {
                int ii;
                for (ii = 0; ii < length && availableBytes - (ii * sizeof(ulong)) > 0; ii++)
                {
                    try
                    {
                        buffer[offset + ii] = reader.ReadUInt64();
                    }
                    catch (EndOfStreamException)
                    {
                        stream.Seek(RESERVED_BYTES, SeekOrigin.Begin);
                        ii--;
                    }
                }
                availableBytes -= ii * sizeof(ulong);
                return ii;
            }
        }
        public int readStrings(string[] buffer, int offset, int length)
        {
            lock (this)
            {
                int ii;
                for (ii = 0; ii < length && availableBytes > 0; ii++)
                {
                    try
                    {
                        long previousPosition = stream.Position;
                        buffer[ii] = reader.ReadString();
                        availableBytes -= (int)(stream.Position - previousPosition);
                    }
                    catch (EndOfStreamException) 
                    {
                        stream.Seek(RESERVED_BYTES, SeekOrigin.Begin);
                        ii--;
                    }
                }
                return ii;
            }
        }

        
    }
}
