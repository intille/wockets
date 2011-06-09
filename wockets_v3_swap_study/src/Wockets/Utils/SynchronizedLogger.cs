using System;
using System.Collections.Generic;
using System.Text;
using System.IO;
using  Wockets.Utils.IPC;
using System.Collections;


namespace Wockets.Utils
{

    public class SynchronizedLogger
    {

        /// <summary>
        /// A system-wide semaphore that serializes writes to the registry
        /// </summary>
        private static String path = "";
        private static String uploadpath = "";
        private static string[] files;
        private const String UPLOAD_FILE = "uploadfile_wockets_";
        //public static ArrayList _Lines = null;
        //private const String RETRY_FILE = "retry.csv";
        //private static ArrayList _NewLines = null;
        //private const String UPLOAD_FILE = "upload_file_";
        


        static SynchronizedLogger()
        {

            #region search for storage card

            string firstCard = "";
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
                        path = "";
                        continue;
                    }
                    //if so, return the path

                    break;
                }
            }


            #endregion


            path += "\\statslog\\";
            uploadpath = path + "upload\\";


            try
            {   
                if (!Directory.Exists(path))
                    Directory.CreateDirectory(path);
            }
            catch
            {
            }

            try
            {
                if (!Directory.Exists(uploadpath))
                    Directory.CreateDirectory(uploadpath);
            }
            catch
            {
            }


            //path += "log.csv";
            //_Lines = new ArrayList();
        }


        #region commented
        //public static void Remove(ArrayList toRemove)
        //{

        //    try
        //    {
        //        ArrayList failedLines=new ArrayList();
        //        for (int i = 0; (i < _Lines.Count); i++)
        //        {
        //            if (!toRemove.Contains(_Lines[i]))
        //                failedLines.Add(_Lines[i]);
        //        }

        //            //if (_NewLines != null){if (_NewLines.Count > 0){
        //            //DateTime now = DateTime.Now;
        //            //String filename = UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + now.Hour + ".csv";

        //        if (failedLines.Count > 0)
        //        {
        //            TextWriter tw = new StreamWriter(uploadpath + RETRY_FILE);
        //            for (int i = 0; (i < failedLines.Count); i++)
        //                tw.WriteLine(failedLines[i]);
        //            tw.Flush();
        //            tw.Close();
        //        }

        //            //}}
        //    }
        //    catch
        //    {
        //        return;
        //    }

        //    for (int i = 0; (i < files.Length); i++)
        //        if (!files[i].Equals(uploadpath + RETRY_FILE))
        //            File.Delete(files[i]);                        
        //}


        //public static void Load()
        //{
           
        //    files = Directory.GetFiles(uploadpath);
        //    _Lines.Clear();


        //    for (int i = 0; (i < files.Length); i++)
        //    {
        //        try
        //        {
        //            TextReader tr = new StreamReader(files[i]);
        //            String line = "";                    
        //            while ((line = tr.ReadLine()) != null)
        //            {
        //                _Lines.Add(line);
        //            }
        //            tr.Close();
        //        }
        //        catch
        //        {
        //        }
        //    }   
        //}
        #endregion 



        public static void Write(String log)
        {

                DateTime now = DateTime.Now;
                TextWriter tw = null;

                //String filename= uploadpath+UPLOAD_FILE+now.Day+"-"+now.Hour+".csv";
                String filename = path + UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + now.Hour + ".csv";
            

                try
                {
                    if (!File.Exists(filename))
                    {

                        #region commented
                        //This part is probaly not very effective, 
                        //I need to pass all file from previous hours to the upload folder, not only one
                        //if (lastFile != "")
                        //    File.Move(path + lastFile, uploadpath + lastFile);
                        #endregion

                        //Move all the files corresponding to previous hours
                        files = Directory.GetFiles(path, UPLOAD_FILE + "*");
                        string mfilename = "";
                        string file_name_ext = "";
                        string[] files_sub_folder = null;

                        for (int i = 0; (i < files.Length); i++)
                        {
                            try
                            {
                                mfilename = files[i].Substring(path.Length);
                                file_name_ext = (mfilename.Split('.'))[0];
                                files_sub_folder = Directory.GetFiles(uploadpath, file_name_ext + "*");
                                
                                if (files_sub_folder.Length > 0)
                                    File.Move(files[i], uploadpath + file_name_ext + "_" + files_sub_folder.Length.ToString() + ".csv");
                                else
                                    File.Move(files[i], uploadpath + mfilename);
                            }
                            catch
                            {
                                //TODO: figureout how can I append the lines to the file in the upload folder 
                                Logger.Error("SynchronizedLogger.cs: Failed to move previous files when invoked in the wc. FileName: " + mfilename );
                            }
                        }

                        //File.Create(filename);
                        //lastFile = UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + now.Hour + ".csv";
                    }

                    tw = new StreamWriter(filename, true);
                    tw.WriteLine(log);
                    tw.Flush();
                    tw.Close();
                    
                }
                catch (Exception e)
                {

                    Logger.Error("SynchronizedLogger.cs: Failed to write summary lines to file when invoked in the wc. FileName: " + filename);
 
                    if (tw != null)
                    {
                        tw.Flush();
                        tw.Close();
                    }
                }
        }



        //public static void Dispose()
        //{
        //     DateTime now = DateTime.Now;
             
        //     //String filename= uploadpath+UPLOAD_FILE+now.Day+"-"+now.Hour+".csv";
        //     //String prevhourfilename= uploadpath+UPLOAD_FILE+now.Day+"-"+now.Hour-1 +".csv";  
             
        //     String filename = UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + now.Hour + ".csv";    
             
        //     now=now.Subtract(new TimeSpan(1,0,0));
        //     String prevhourfilename = UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + (now.Hour - 1) + ".csv"; 


        //     if (File.Exists(path + filename))             
        //         File.Move(path + filename, uploadpath + filename);

        //     if (File.Exists(path + prevhourfilename))
        //         File.Move(path + prevhourfilename, uploadpath + prevhourfilename);             
                
        //}



        //public static void Flush()
        //{
        //    //TextWriter tw = new StreamWriter(path, true);
        //    //String filename= uploadpath+UPLOAD_FILE+now.Day+"-"+now.Hour+".csv";

        //    DateTime now = DateTime.Now;
        //    TextWriter tw = null;
        //    String filename = UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + now.Hour + ".csv";


        //    try
        //    {


        //        #region commented
        //        //if (lastFile != "")
        //        //    File.Move(path + lastFile, uploadpath + lastFile);
        //        //File.Create(filename);
        //        //lastFile = UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + now.Hour + ".csv";
        //        #endregion


        //        if (!File.Exists(path + filename))
        //        {
        //            //Move all the files corresponding to previous hours
        //            files = Directory.GetFiles(path, UPLOAD_FILE + "*");
        //            string mfilename = "";

        //            for (int i = 0; (i < files.Length); i++)
        //            {
        //                mfilename = files[i].Substring(path.Length);
        //                File.Move(files[i], uploadpath + mfilename);
        //            }
        //        }


        //        if (_Lines.Count > 0)
        //        {
        //            tw = new StreamWriter(path + filename, true);
        //            for (int i = 0; (i < _Lines.Count); i++)
        //                tw.WriteLine(_Lines[i]);

        //            tw.Flush();
        //            tw.Close();
        //            tw = null;
        //        }


        //    }
        //    catch (Exception e)
        //    {
        //        if (tw != null)
        //        {
        //            tw.Flush();
        //            tw.Close();
        //        }
        //    }
        //}



        public static void Flush()
        {
            string mfilename = "";
            string file_name_prefix = "";
            string[] files_sub_folder = null;
            

            // when closing, move all the files corresponding to previous hours
            files = Directory.GetFiles(path, UPLOAD_FILE + "*");


            for (int i = 0; i < files.Length; i++)
            {
                mfilename = files[i].Substring(path.Length);

                if (!File.Exists(uploadpath + mfilename))
                {
                    try
                    {
                        File.Move(files[i], uploadpath + mfilename);   
                    }
                    catch
                    { //Error("Failed to move previous files when invoked in the wc. FileName: " + mfilename );  
                    }
                }
                else
                {
                    file_name_prefix = (mfilename.Split('.'))[0];
                    files_sub_folder = Directory.GetFiles(uploadpath, file_name_prefix + "*");

                    try
                    {
                        if (!File.Exists(uploadpath + file_name_prefix + "_" + files_sub_folder.Length.ToString() + ".csv"))
                            File.Move(files[i], uploadpath + file_name_prefix + "_" + files_sub_folder.Length.ToString() + ".csv");
                        else
                            File.Move(files[i], uploadpath + file_name_prefix + "_" + (files_sub_folder.Length + 1).ToString() + ".csv");
                    }
                    catch
                    { //Error("Failed to move previous files when invoked in the wc. FileName: " + mfilename );
                    }
                }
            }

        }



    }
}
