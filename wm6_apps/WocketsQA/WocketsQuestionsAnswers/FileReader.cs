using System;
using System.Collections.Generic;
using System.Text;
using System.IO;

namespace Wockets
{
    public class FileReader
    {
        private String fileName = null;
        private StreamReader streamReader = null;
        private FileStream fileStream = null;
        private bool validFile = false;

        /// <summary>
        /// Check if a valid file.
        /// </summary>
        /// <returns>Returns true if file is valid</returns>
        public bool IsValidFile()
        {
            return validFile;
        }

        /// <summary>
        /// Initialize with a string
        /// </summary>
        /// <param name="aFileName">String filename</param>
        public FileReader(String aFileName)
        {
            this.fileName = aFileName;
        }

        private void SignalError(String s)
        {
            //CloseFile();
            //Console.WriteLine("Error in StringReader: " + s + " for file: " + fileName);
        }

        private void SignalError(Exception e, String s)
        {
            //CloseFile();
            //Console.WriteLine("Error in StringReader: " + e.Message + " " + s + " for file: " + fileName);
        }

        /// <summary>
        /// Open the file to read.
        /// </summary>
        public void OpenFile()
        {
            try
            {
                fileStream = new FileStream(fileName, FileMode.Open, FileAccess.Read);
            }
            catch (Exception e)
            {
                //May be read only so try again
                try
                {
                    fileStream = new FileStream(fileName, FileMode.Open, FileAccess.Read);
                }
                catch (Exception e2)
                {
                    SignalError(e2, "Can't find file " + fileName + "\n" + e.ToString());
                    return;
                }

            }
            validFile = true;

            streamReader = new StreamReader(fileStream);
        }

        /// <summary>
        /// Close the file after reading.
        /// </summary>
        public void CloseFile()
        {
            try
            {
                if (streamReader != null)
                    streamReader.Close();
                else
                    SignalError("Could not close " + fileName + " because file not opened!");
            }
            catch (IOException e)
            {
                SignalError(e, "Error closing " + fileName + " file");
            }
        }

        /// <summary>
        /// Read a single line from the file as a String
        /// </summary>
        /// <returns>The String line</returns>
        public String ReadLine()
        {
            if (!validFile)
            {
                SignalError("Can't read. File not opened:" + fileName);
                return null;
            }
            try
            {
                if (streamReader != null)
                    return streamReader.ReadLine();
                else
                    SignalError("Problem with StreamReader during read");
            }
            catch (IOException e)
            {
                SignalError(e, "Error reading a line from " + fileName);
                return null;
            }
            return null;
        }
    }
}