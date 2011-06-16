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

        //TODO: add log lines for this uploader
        public  static ArrayList _Lines = null;
        private static ArrayList _NewLines = null;
        private static string[] files;
        
        private const String RETRY_FILE = "retry.csv";
        private static string RETRY_FILE_PREFIX = "";
        


        static UploadSynchronizedLogger()
        {


            #region search for storage card

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


    }
}
