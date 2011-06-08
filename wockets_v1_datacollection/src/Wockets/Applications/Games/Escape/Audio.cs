using System;
using System.Runtime.InteropServices;
using System.Diagnostics;
using System.Threading;
using System.IO;
using Wockets.Utils;
using System.Windows.Forms;

namespace Wockets.Applications.Games.Escape
{
    public class Audio
    {
        private byte[] m_soundBytes;
        private string m_fileName;

        private enum Flags
        {
            SND_SYNC = 0x0000,  /* play synchronously (default) */
            SND_ASYNC = 0x0001,  /* play asynchronously */
            SND_NODEFAULT = 0x0002,  /* silence (!default) if sound not found */
            SND_MEMORY = 0x0004,  /* pszSound points to a memory file */
            SND_LOOP = 0x0008,  /* loop the sound until next sndPlaySound */
            SND_NOSTOP = 0x0010,  /* don't stop any currently playing sound */
            SND_NOWAIT = 0x00002000, /* don't wait if the driver is busy */
            SND_ALIAS = 0x00010000, /* name is a registry alias */
            SND_ALIAS_ID = 0x00110000, /* alias is a predefined ID */
            SND_FILENAME = 0x00020000, /* name is file name */
            SND_RESOURCE = 0x00040004  /* name is resource name or atom */
        }

        [DllImport("CoreDll.DLL", EntryPoint = "PlaySound", SetLastError = true)]
        private extern static int WCE_PlaySound(string szSound, IntPtr hMod, int flags);

        [DllImport("CoreDll.DLL", EntryPoint = "PlaySound", SetLastError = true)]
        private extern static int WCE_PlaySoundBytes(byte[] szSound, IntPtr hMod, int flags);



        /// <summary>
        /// Construct the Sound object to play sound data from the specified file.
        /// </summary>
        public Audio(string fileName)
        {
            m_fileName = fileName;
        }


        /// <summary>
        /// Construct the Sound object to play sound data from the specified stream.
        /// </summary>
        public Audio(Stream stream)
        {
            // read the data from the stream
            m_soundBytes = new byte[stream.Length];
            stream.Read(m_soundBytes, 0, (int)stream.Length);
        }

        /// <summary>
        /// Play the sound
        /// </summary>
        public void Play()
        {
            // if a file name has been registered, call WCE_PlaySound, 
            //  otherwise call WCE_PlaySoundBytes
            if (m_fileName != null)
                WCE_PlaySound(m_fileName, IntPtr.Zero, (int)(Flags.SND_ASYNC | Flags.SND_FILENAME));
            else
                WCE_PlaySoundBytes(m_soundBytes, IntPtr.Zero, (int)(Flags.SND_ASYNC | Flags.SND_MEMORY));
            this.AudioTime(this.m_fileName);
            Thread.Sleep((int)(this.timeSecs * 1000));
        }

        public void Loop()
        {
            WCE_PlaySound(m_fileName, IntPtr.Zero, (int)(Flags.SND_LOOP | Flags.SND_FILENAME));
        }

        public void Stop()
        {
            int hresult = WCE_PlaySound(null, IntPtr.Zero, (int)(Flags.SND_SYNC | Flags.SND_FILENAME));
        }










        private ByteReader br;
        private ByteWriter bw;

        /// <summary>
        /// Total bytes in Wav file data.
        /// </summary>
        public int totalBytes = 0;

        /// <summary>
        /// The number of channels of data (1 or 2). 
        /// </summary>
        public int channels = 0;

        /// <summary>
        /// The time of the Wav in seconds.
        /// </summary>
        public double timeSecs = 0;

        /// <summary>
        /// The sample rate (e.g., 22050).
        /// </summary>
        public int sampleRate = 0;

        /// <summary>
        /// The byte rate each second.
        /// </summary>
        public int byteRate = 0;

        /// <summary>
        /// The bits per sample (16 or 8). 
        /// </summary>
        public int bps = 0;

        /// <summary>
        /// The total number of sound samples in the file.
        /// </summary>
        public int totalSamples = 0;

        /// <summary>
        /// Indicates if the WavInfo object has been successfully loaded. 
        /// </summary>
        public bool isLoaded = false;

        /// <summary>
        /// Construct object to read/write wavs.
        /// </summary>
        public Audio()
        {

        }

        /// <summary>
        /// The data (interleaved with stereo)
        /// </summary>
        public int[] someData;

        /// <summary>
        /// Get the data. 
        /// </summary>
        /// <returns></returns>
        public int[] GetData()
        {
            return someData;
        }

        private byte[] subchunk2sizebytes = new byte[4];
        private byte[] subchunk1sizebytes = new byte[4];

        /// <summary>
        /// Stores the string for the last error.
        /// </summary>
        public static string lastErrorStr = "";

        /// <summary>
        /// An object that loads the Wav header data from the supplied filename. 
        /// </summary>
        /// <param name="aFileName">A valid Wav file in uncompressed PCM format.</param>
        public void AudioTime(string aFileName)
        {
            try
            {
                //lastErrorStr = "Before ByteReader. ";
                br = new ByteReader(aFileName);
                //lastErrorStr += "Before OpenFile. ";
                br.OpenFile();
                byte[] aByte = new byte[1];

                // Skip RIFF header 
                //lastErrorStr += "Before read header. ";
                byte[] someBytes = new byte[4];
                br.ReadBytes(someBytes);

                // Read the size of the file
                br.ReadByte(aByte);
                byte b4 = aByte[0];
                br.ReadByte(aByte);
                byte b3 = aByte[0];
                br.ReadByte(aByte);
                byte b2 = aByte[0];
                br.ReadByte(aByte);
                byte b1 = aByte[0];
                someBytes[3] = b1;
                someBytes[2] = b2;
                someBytes[1] = b3;
                someBytes[0] = b4;
                // Reconstruct into an int			
                totalBytes = BitConverter.ToInt32(someBytes, 0);
                totalBytes = totalBytes - 36;
                //Console.WriteLine ("TotalBytes: " + totalBytes);
                //lastErrorStr += "TotalBytes: " + totalBytes + ". ";

                // Skip 
                for (int i = 0; i < 8; i++)
                    br.ReadByte(aByte);

                br.ReadBytes(subchunk1sizebytes);

                // Audio format
                for (int i = 0; i < 2; i++)
                    br.ReadByte(aByte);

                // channels 
                br.ReadByte(aByte);
                b2 = aByte[0];
                br.ReadByte(aByte);
                b1 = aByte[0];
                someBytes[3] = 0;
                someBytes[2] = 0;
                someBytes[1] = b1;
                someBytes[0] = b2;
                // Reconstruct into an int			
                channels = BitConverter.ToInt32(someBytes, 0);
                //Console.WriteLine ("Channels: " + channels);
                //lastErrorStr += "Channels: " + channels + ". ";

                // Read the sampleRate
                br.ReadByte(aByte);
                b4 = aByte[0];
                br.ReadByte(aByte);
                b3 = aByte[0];
                br.ReadByte(aByte);
                b2 = aByte[0];
                br.ReadByte(aByte);
                b1 = aByte[0];
                someBytes[3] = b1;
                someBytes[2] = b2;
                someBytes[1] = b3;
                someBytes[0] = b4;
                // Reconstruct into an int			
                sampleRate = BitConverter.ToInt32(someBytes, 0);
                //Console.WriteLine ("SampleRate: " + sampleRate);
                //lastErrorStr += "SampleRate: " + sampleRate + ". ";

                // Read the byteRate
                br.ReadByte(aByte);
                b4 = aByte[0];
                br.ReadByte(aByte);
                b3 = aByte[0];
                br.ReadByte(aByte);
                b2 = aByte[0];
                br.ReadByte(aByte);
                b1 = aByte[0];
                someBytes[3] = b1;
                someBytes[2] = b2;
                someBytes[1] = b3;
                someBytes[0] = b4;
                // Reconstruct into an int			
                byteRate = BitConverter.ToInt32(someBytes, 0);

                if (byteRate != 0)
                    timeSecs = (double)totalBytes / ((double)byteRate);
                else
                    timeSecs = 0;

                br.CloseFile();

                /*
                TextWriter tw = new StreamWriter("SoundTest.txt", true);
                tw.WriteLine(this.timeSecs + ", " + aFileName);
                tw.Close();
                */


            }
            catch (Exception e)
            {
                lastErrorStr += "WavInfo:WavInfo: ERROR: Error loading WavData: " + e.ToString();
                if (br != null)
                    br.CloseFile();
                isLoaded = false;
            }
        }

        /// <summary>
        /// Write a Wav file in uncompressed PCM format.
        /// </summary>
        /// <param name="aFileName">File to save wav into.</param>
        public void WriteWav(string aFileName)
        {
            try
            {
                bw = new ByteWriter(aFileName, true);
                bw.OpenFile();
                byte[] aByte = new byte[1];

                // Write RIFF header 
                byte[] someBytes = new byte[4];
                someBytes[0] = (byte)'R';
                someBytes[1] = (byte)'I';
                someBytes[2] = (byte)'F';
                someBytes[3] = (byte)'F';
                bw.WriteBytes(someBytes);

                // Write the size of the file (totalBytes + 36)
                int tot = totalBytes + 36;
                someBytes = BitConverter.GetBytes(tot);
                byte b4 = someBytes[0];
                byte b3 = someBytes[1];
                byte b2 = someBytes[2];
                byte b1 = someBytes[3];
                bw.WriteBytes(someBytes);

                someBytes[0] = (byte)'W';
                someBytes[1] = (byte)'A';
                someBytes[2] = (byte)'V';
                someBytes[3] = (byte)'E';
                bw.WriteBytes(someBytes);

                someBytes = new byte[4];
                someBytes[0] = (byte)'f';
                someBytes[1] = (byte)'m';
                someBytes[2] = (byte)'t';
                someBytes[3] = (byte)' ';
                bw.WriteBytes(someBytes);

                // Write subchunk1size 
                bw.WriteBytes(subchunk1sizebytes);

                // PCM format (1) 
                b1 = 0x01;
                bw.WriteByte(b1);
                b1 = 0x00;
                bw.WriteByte(b1);

                // channels (1 or 2)
                b1 = (byte)channels;
                bw.WriteByte(b1);
                b1 = 0x00;
                bw.WriteByte(b1);

                // Write the sampleRate
                someBytes = BitConverter.GetBytes(sampleRate);
                b1 = someBytes[3];
                b2 = someBytes[2];
                b3 = someBytes[1];
                b4 = someBytes[0];
                bw.WriteByte(b4);
                bw.WriteByte(b3);
                bw.WriteByte(b2);
                bw.WriteByte(b1);

                // Write the byteRate
                someBytes = BitConverter.GetBytes(byteRate);
                b1 = someBytes[3];
                b2 = someBytes[2];
                b3 = someBytes[1];
                b4 = someBytes[0];
                bw.WriteByte(b4);
                bw.WriteByte(b3);
                bw.WriteByte(b2);
                bw.WriteByte(b1);

                // Block align (2) 
                b1 = 0x02;
                bw.WriteByte(b1);
                b1 = 0x00;
                bw.WriteByte(b1);

                // BPS
                someBytes = BitConverter.GetBytes(bps);
                b1 = someBytes[1];
                b2 = someBytes[0];
                bw.WriteByte(b2);
                bw.WriteByte(b1);

                someBytes[0] = (byte)'d';
                someBytes[1] = (byte)'a';
                someBytes[2] = (byte)'t';
                someBytes[3] = (byte)'a';
                bw.WriteBytes(someBytes);

                // Subchunk2size 
                int subchunk2 = someData.Length * 2; //samples *channels * bps / 8;
                someBytes = BitConverter.GetBytes(subchunk2);
                b1 = someBytes[3];
                b2 = someBytes[2];
                b3 = someBytes[1];
                b4 = someBytes[0];
                bw.WriteByte(b4);
                bw.WriteByte(b3);
                bw.WriteByte(b2);
                bw.WriteByte(b1);

                // Subchunk2size 2048
                // bw.WriteBytes(subchunk2sizebytes);

                // Write the data
                for (int i = 0; i < someData.Length; i++)
                {
                    someBytes = BitConverter.GetBytes(someData[i]);
                    b1 = someBytes[1];
                    b2 = someBytes[0];
                    bw.WriteByte(b2);
                    bw.WriteByte(b1);
                }
                bw.CloseFile();
            }
            catch (Exception e)
            {
                if (bw != null)
                    bw.CloseFile();
            }
        }
    }

}