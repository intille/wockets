using System;
using System.Collections.Generic;
using System.Text;
using System.IO;
//using Wockets.Utils.IPC;
using System.Collections;


namespace Wockets.Utils
{

    /// <summary>
    /// 
    /// </summary>
    public class CustomSynchronizedLogger
    {

        private String path = "";
        private String uploadpath = "";
        private String UPLOAD_FILE = "uploadfile_";
        private string[] files;




        /// <summary>
        /// 
        /// </summary>
        public CustomSynchronizedLogger(string data_type)
        {

            path = getStorageCard();

            if( data_type.CompareTo("events") == 0)
               UPLOAD_FILE += "events_"; 
            else if( data_type.CompareTo("qa") == 0)
               UPLOAD_FILE += "qa_"; 
            
            path += "\\statslog\\";
            uploadpath = path + "upload\\";


            try
            {
                if (!Directory.Exists(path))
                    Directory.CreateDirectory(path);
            }
            catch
            {
                //Failed to create path directory
            }

            try
            {
                if (!Directory.Exists(uploadpath))
                    Directory.CreateDirectory(uploadpath);
            }
            catch
            {
                //Failed to create upload path directory
            }

         
        }

        private static string getStorageCard()
        {
            String path = WocketsQuestionsAnswers.Program.MOCK_STORAGE_LOCATION;
            {
                string firstCard = "";
                try
                {
                    System.IO.DirectoryInfo di = new System.IO.DirectoryInfo("\\");
                    System.IO.FileSystemInfo[] fsi = di.GetFileSystemInfos();
                    //iterate through them
                    for (int x = 0; x < fsi.Length; x++)
                    {
                        //check to see if this is a temporary storage card (e.g. SD card)
                        if ((fsi[x].Attributes & System.IO.FileAttributes.Temporary) == System.IO.FileAttributes.Temporary)
                        {
                            path = fsi[x].FullName;
                            try
                            {
                                Directory.CreateDirectory(firstCard + "\\writable");
                                Directory.Delete(firstCard + "\\writable");
                            }
                            catch (Exception)
                            {
                                path = WocketsQuestionsAnswers.Program.MOCK_STORAGE_LOCATION;
                                continue;
                            }
                            //if so, return the path
                            break;
                        }
                    }
                }
                catch { }
            }
            return path;
        }

        public void Write(String log)
            {

                DateTime now = DateTime.Now;
                TextWriter tw = null;

                string filename = path + UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + now.Hour + ".csv";
            

                try
                {
                    if (!File.Exists(filename))
                    {

                        //Move all the files corresponding to previous hours
                        files = Directory.GetFiles(path, UPLOAD_FILE + "*");
                        string mfilename = "";

                        for (int i = 0; (i < files.Length); i++)
                        {
                            try
                            {
                                mfilename = files[i].Substring(path.Length);
                                File.Move(files[i], uploadpath + mfilename);
                            }
                            catch
                            {
                                //TODO: Check the logger do not cause problems in the system wide logger
                                //Error("Failed to move previous files when invoked in the wc. FileName: " + mfilename );
                            }
                        }
                    }
                    tw = new StreamWriter(filename, true);
                    tw.WriteLine(log);
                    tw.Flush();
                    tw.Close();
                    
                }
                catch
                {

                    //Error("Failed to write summary lines to file when invoked in the wc. FileName: " + filename);
                    if (tw != null)
                    {
                        tw.Flush();
                        tw.Close();
                    }

                }
        }



        public void Dispose()
        {

            DateTime now = DateTime.Now;
            String filename = UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + now.Hour + ".csv";

            now = now.Subtract(new TimeSpan(1, 0, 0));
            String prevhourfilename = UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + (now.Hour - 1) + ".csv";


            try
            {
                if (File.Exists(path + filename))
                    if (!File.Exists(uploadpath + filename))
                        File.Move(path + filename, uploadpath + filename);
                    else
                        AppendLinesToFile(path + filename, uploadpath + filename);


                if (File.Exists(path + prevhourfilename))
                    if (!File.Exists(uploadpath + prevhourfilename))
                        File.Move(path + prevhourfilename, uploadpath + prevhourfilename);
                    else
                        AppendLinesToFile(path + prevhourfilename, uploadpath + prevhourfilename);
            }
            catch
            { 
                //Failed to dispose CustomSynchronizedLogger Class
            }

        }



        private void AppendLinesToFile(string source_file, string destination_file)
        {

            try
            {

                TextReader tr = new StreamReader(source_file);
                String line = "";
                ArrayList _Lines = null;

                while ((line = tr.ReadLine()) != null)
                {
                    _Lines.Add(line);
                }
                tr.Close();


                if ( _Lines != null )
                {
                    TextWriter tw = new StreamWriter(destination_file, true);
                    for (int i = 0; i < _Lines.Count; i++)
                      tw.WriteLine(_Lines[i]);
                    
                    tw.Flush();
                    tw.Close();
                }


            }
            catch
            {
                // Failed to append lines to destination files
            }

        }



        public void Flush()
        {

            DateTime now = DateTime.Now;
            TextWriter tw = null;
            String filename = UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + now.Hour + ".csv";


            try
            {

                if (!File.Exists(path + filename))
                {
                    //Move all the files corresponding to previous hours
                    files = Directory.GetFiles(path, UPLOAD_FILE + "*");
                    string mfilename = "";

                    for (int i = 0; (i < files.Length); i++)
                    {
                        mfilename = files[i].Substring(path.Length);

                        if (!File.Exists(uploadpath + mfilename))
                            File.Move(files[i], uploadpath + mfilename);
                        else
                            AppendLinesToFile(files[i], uploadpath + mfilename);
                    }

                }

            }
            catch (Exception e)
            {
                // Failed to flush file of customSynchronizedLogger Class
                if (tw != null)
                {
                    tw.Flush();
                    tw.Close();
                }
            }
        }
    }
}

