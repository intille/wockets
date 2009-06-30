using System;
using System.Collections.Generic;
using System.Text; //Encoding
using System.Collections;//ArrayList
using System.IO;

namespace MobiRnD_RDT.Utilities
{
    public class FileReadWrite
    {
        #region SAVE TEXT TO FILE
        public static bool SaveTextToFile(string filepath, string content, bool append)
        {
            return SaveLinesToFile(filepath, new string[1] { content }, append);
        }
        public static bool SaveLinesToFile(string filepath, ArrayList content, bool append)
        {
            return SaveLinesToFile(filepath, (string[])content.ToArray(typeof(string)), append);
        }
        public static bool SaveLinesToFile(string filepath, string[] content, bool append)
        {
            bool isSuccess = false;

            StreamWriter sr = null;
            try
            {
                lock (typeof(FileReadWrite))
                {
                    if (append && File.Exists(filepath))
                        sr = File.AppendText(filepath);
                    else
                        sr = File.CreateText(filepath);

                    for (int i = 0; i < content.Length; i++)
                    {
                        sr.WriteLine(content[i]);
                    }
                    sr.Close();
                }
                isSuccess = true;
            }
            catch (Exception ex)
            {
                throw (ex);
            }
            finally
            {
                if (sr != null) sr.Close();
            }

            return isSuccess;

        }

        public static void ResetFile(string filepath)
        {
            if (File.Exists(filepath))
            {
                FileStream fs = null;

                try
                {
                    fs = File.Open(filepath, FileMode.Truncate);
                }
                catch (Exception ex)
                {
                    throw (ex);
                }
                finally
                {
                    if (fs != null)
                    {
                        fs.Close();
                        fs = null;
                    }
                }
            }
            else throw (new FileNotFoundException(filepath));
        }
        #endregion

        #region READ TEXT FROM FILE
        public static string ReadTextFromFile(string filepath)
        {
            string readtext = "";

            if (File.Exists(filepath))
            {
                lock (typeof(FileReadWrite))
                {
                    using (StreamReader sr = new StreamReader(filepath))
                    {
                        readtext = sr.ReadToEnd();
                    }
                }

            }
            else throw (new FileNotFoundException(filepath));

            return readtext;

        }

        public static string[] ReadLinesFromFile(string filepath)
        {
            string[] lines = new string[0];


            lines = (string[])ReadListFromFile(filepath).ToArray(typeof(string));

            return lines;

        }

        public static ArrayList ReadListFromFile(string filepath)
        {
            ArrayList alLines = new ArrayList();

            if (File.Exists(filepath))
            {
                StreamReader sr = null;
                try
                {
                    lock (typeof(FileReadWrite))
                    {
                        sr = new StreamReader(filepath, Encoding.Default);
                        string line = "";
                        while ((line = sr.ReadLine()) != null)
                        {
                            alLines.Add(line);
                        }
                        sr.Close();
                    }
                }
                catch (Exception ex)
                {
                    throw (ex);
                }
                finally
                {
                    if (sr != null) sr.Close();
                }
            }
            else throw (new FileNotFoundException(filepath));


            return alLines;

        }
        #endregion

        #region BINARY FILES
        public static byte[] GetBinaryFile(string filepath)
        {
            byte[] binaryfile = new byte[0];
            FileStream fs = null;
            if (File.Exists(filepath))
            {
                try
                {
                    fs = File.OpenRead(filepath);
                    binaryfile = ConvertStreamToByteBuffer(fs);
                }
                catch (Exception ex)
                {
                    throw (ex);
                }
                finally
                {
                    if (fs != null) fs.Close();
                }

            }
            else throw (new FileNotFoundException(filepath));

            return binaryfile;
        }

        public static byte[] ConvertStreamToByteBuffer(Stream fstream)
        {
            int b;
            byte[] filebytes = new byte[0];
            MemoryStream tempStream = null;
            try
            {
                tempStream = new MemoryStream();
                while ((b = fstream.ReadByte()) != -1)
                {
                    tempStream.WriteByte((byte)b);
                }
                filebytes = tempStream.ToArray();
            }
            catch (Exception ex)
            {
                throw (ex);
            }
            finally
            {
                if (tempStream != null) tempStream.Close();
            }
            return filebytes;
        }


        public static bool SaveToFile(string filePath, byte[] bytestosave)
        {
            bool isSuccess = false;

            FileStream fs = null;
            BinaryWriter bw = null;
            try
            {
                //create (overwrite if necessary) filestream
                fs = new FileStream(filePath, FileMode.Create);

                //create the writer for data
                bw = new BinaryWriter(fs);

                //write data to file
                for (int i = 0; i < bytestosave.Length; i++)
                {
                    bw.Write(bytestosave[i]);
                }
                isSuccess = true;
            }
            catch (Exception ex)
            {
                throw (ex);
            }
            finally
            {
                //close streams
                if (bw != null) bw.Close();
                if (fs != null) fs.Close();
            }

            return isSuccess;
        }

        #endregion

        #region DIRECTORY INFORMATION
        public static string ExeDirectory
        {
#if (SP || PPC || Smartphone || PocketPC)
            get { return Path.GetDirectoryName(System.Reflection.Assembly.GetCallingAssembly().GetName().CodeBase); }
#else
            get { return Path.GetDirectoryName(AppDomain.CurrentDomain.BaseDirectory); }
#endif
        }
        #endregion

    }
}
