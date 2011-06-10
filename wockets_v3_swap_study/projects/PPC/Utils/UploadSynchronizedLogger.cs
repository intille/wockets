using System;
using System.Collections.Generic;
using System.Text;
using System.IO;
using Wockets.Utils.IPC;
using System.Collections;



namespace Wockets.Utils
{

    public class UploadSynchronizedLogger
    {

        private static String path = "";
        private static String uploadpath = "";

        //TODO: add logs lines for this uploader
        //TODO: add the suspend prevent code to ensure that the connection is stablished
        //TODO: ensure we have network connectivity with wifi, 
        //      otherwise, re-route, and ensure we log this info
        public  static ArrayList _Lines = null;
        private static ArrayList _NewLines = null;
        private static string[] files;
        
        private const String RETRY_FILE = "retry.csv";
        private static string RETRY_FILE_PREFIX = "";
        

        static UploadSynchronizedLogger()
        {

            #region search for storage card

            #region commented
            //string firstCard = "";
            //System.IO.DirectoryInfo di = new System.IO.DirectoryInfo("\\");
            //System.IO.FileSystemInfo[] fsi = di.GetFileSystemInfos();


            ////iterate through them
            //for (int x = 0; x < fsi.Length; x++)
            //{
            //    //check to see if this is a temporary storage card (e.g. SD card)
            //    if ((fsi[x].Attributes & System.IO.FileAttributes.Temporary) == System.IO.FileAttributes.Temporary)
            //    {
            //        path = fsi[x].FullName;
            //        try
            //        {
            //            Directory.CreateDirectory(firstCard + "\\writable");
            //            Directory.Delete(firstCard + "\\writable");
            //        }
            //        catch (Exception)
            //        {
            //            path = "";
            //            continue;
            //        }
            //        //if so, return the path

            //        break;
            //    }
            //}
            #endregion

            int TIMEOUT_SECONDS = 2;
            int number_of_trials = -1;
            string firstCard = "";
            bool is_card_found = false;
            System.IO.DirectoryInfo di;
            System.IO.FileSystemInfo[] fsi;


            while (number_of_trials < TIMEOUT_SECONDS && !is_card_found)
            {

                try
                {
                    di = new System.IO.DirectoryInfo("\\");
                    fsi = di.GetFileSystemInfos();

                    //iterate through them
                    for (int x = 0; x < fsi.Length; x++)
                    {
                        //check to see if this is a temporary storage card (e.g. SD card)
                        if ((fsi[x].Attributes & System.IO.FileAttributes.Temporary) == System.IO.FileAttributes.Temporary)
                        {
                            //Verify if is indeed writable
                            firstCard = fsi[x].FullName;
                            try
                            {
                                Directory.CreateDirectory(firstCard + "\\writable");
                                Directory.Delete(firstCard + "\\writable");
                                is_card_found = true;
                            }
                            catch (Exception)
                            {
                                firstCard = "";
                                
                            }
                            break;
                        }
                    }
                }
                catch
                { }

                number_of_trials++;
            }

            
            #endregion


            path = firstCard + "\\statslog\\";
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


            _Lines = new ArrayList();

        }



        public static void Load()
        {

            files = Directory.GetFiles(uploadpath);
            _Lines.Clear();


            //Get all the summary info lines from files
            for (int i = 0; (i < files.Length); i++)
            {
                try
                {
                    TextReader tr = new StreamReader(files[i]);
                    String line = "";
                    while ((line = tr.ReadLine()) != null)
                    {
                        _Lines.Add(line);
                    }
                    tr.Close();
                }
                catch
                {

                }

            }
        }




        public static void Remove(ArrayList toRemove)
        {
            bool success = false;
            TextWriter tw = null;
            ArrayList failedLines = new ArrayList();


            try
            {
               
                for (int i = 0; (i < _Lines.Count); i++)
                {
                    if (!toRemove.Contains(_Lines[i]))
                        failedLines.Add(_Lines[i]);
                }


                DateTime now = DateTime.Now;
                RETRY_FILE_PREFIX = now.ToString("yyyy-MM-dd") + "_" + now.ToString("hh-mm-ss") + "_";
                tw = new StreamWriter(uploadpath + RETRY_FILE_PREFIX + RETRY_FILE);
                
                
                for (int i = 0; (i < failedLines.Count); i++)
                    tw.WriteLine(failedLines[i]);

                tw.Flush();
                tw.Close();
                tw = null;
                
                success = true;      
            }
            catch
            {
                if (tw != null)
                {
                    tw.Flush();
                    tw.Close();
                    tw = null;
                }

                return;
            }


            //cleanup files
            if (success)
            {
                for (int i = 0; (i < files.Length); i++)
                    if (!files[i].Equals(uploadpath + RETRY_FILE_PREFIX + RETRY_FILE))
                        File.Delete(files[i]);
            }
            else
            {
                for (int i = 0; (i < files.Length); i++)
                    if ( !files[i].EndsWith(RETRY_FILE) )
                        File.Delete(files[i]);
            }  

        }


      

        #region commented

        //public static void Write(String log)
        //{

        //        DateTime now = DateTime.Now;
        //        TextWriter tw = null;

        //        //String filename= uploadpath+UPLOAD_FILE+now.Day+"-"+now.Hour+".csv";
        //        String filename = path + UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + now.Hour + ".csv";
            
                
                
        //        try
        //        {
        //            if (!File.Exists(filename))
        //            {

        //                #region commented
        //                //This part is probaly not very effective, 
        //                //I need to pass all file from previous hours to the upload folder, not only one
        //                //if (lastFile != "")
        //                //    File.Move(path + lastFile, uploadpath + lastFile);
        //                #endregion

        //                //Move all the files corresponding to previous hours
        //                files = Directory.GetFiles(path, UPLOAD_FILE + "*");
        //                string mfilename = "";

        //                for (int i = 0; (i < files.Length); i++)
        //                {
        //                    try
        //                    {
        //                        mfilename = files[i].Substring(path.Length);
        //                        File.Move(files[i], uploadpath + mfilename);
        //                    }
        //                    catch
        //                    {
        //                        //TODO: figureout how can I append the lines to the file in the upload folder 
        //                        Logger.Error("SynchronizedLogger.cs: Failed to move previous files when invoked in the wc. FileName: " + mfilename );
        //                    }
        //                }

        //                //File.Create(filename);
        //                //lastFile = UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + now.Hour + ".csv";
        //            }

        //            tw = new StreamWriter(filename, true);
        //            tw.WriteLine(log);
        //            tw.Flush();
        //            tw.Close();
                    
        //        }
        //        catch (Exception e)
        //        {

        //            Logger.Error("SynchronizedLogger.cs: Failed to write summary lines to file when invoked in the wc. FileName: " + filename);
 
        //            if (tw != null)
        //            {
        //                tw.Flush();
        //                tw.Close();
        //            }

        //        }
        //}

        #endregion 


        #region commented
        //public static void Dispose()
        //{
        //     DateTime now = DateTime.Now;
              
        //     String filename = UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + now.Hour + ".csv";    
             
        //     now=now.Subtract(new TimeSpan(1,0,0));
        //     String prevhourfilename = UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + (now.Hour - 1) + ".csv"; 


        //     if (File.Exists(path + filename))             
        //         File.Move(path + filename, uploadpath + filename);

        //     if (File.Exists(path + prevhourfilename))
        //         File.Move(path + prevhourfilename, uploadpath + prevhourfilename);             

        //}
        #endregion 


        #region commented
        //public static void Flush()
        //{
        //   DateTime now = DateTime.Now;
        //   TextWriter tw = null;
        //   String filename = UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + now.Hour + ".csv";
                
            
        //    try
        //    {
                

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
        //    catch(Exception e)
        //    {

        //        // The Upload Synchronized Logger Failed to Flush Lines to File
        //        if (tw != null)
        //        {
        //            tw.Flush();
        //            tw.Close();
        //        }

        //    }         
        //}
        #endregion 


    }
}
