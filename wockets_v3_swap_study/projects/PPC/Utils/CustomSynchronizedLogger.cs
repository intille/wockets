using System;
using System.Collections.Generic;
using System.Text;
using System.IO;
using  Wockets.Utils.IPC;
using System.Collections;
//using System.Threading;



namespace Wockets.Utils
{

    /// <summary>
    /// 
    /// </summary>
    public class CustomSynchronizedLogger
    {

        public  String path = "";
        public  String uploadpath = "";
        private String UPLOAD_FILE = "uploadfile_";
        private string[] files;


        public CustomSynchronizedLogger(string data_type, string firstCard, out bool result)
        {
           result = Initialize(data_type, firstCard);
           
        }



       private bool Initialize(string data_type, string firstCard)
       {
            path = "";
            string storage_card = "";
            bool suceess = false;

            // Add specific file identification indexes
            if (data_type.CompareTo("events") == 0)
                UPLOAD_FILE += "events_";
            else if (data_type.CompareTo("qa") == 0)
                UPLOAD_FILE += "qa_";
            else if (data_type.CompareTo("wockets") == 0)
                UPLOAD_FILE += "wockets_"; 

           
            #region search for storage card

            if (firstCard.Length == 0)
            {
                #region commented
                //string tmp_firstCard = "";
                //System.IO.DirectoryInfo di = new System.IO.DirectoryInfo("\\");
                //System.IO.FileSystemInfo[] fsi = di.GetFileSystemInfos();

                ////iterate through them
                //for (int x = 0; x < fsi.Length; x++)
                //{
                //    //check to see if this is a temporary storage card (e.g. SD card)
                //    if ((fsi[x].Attributes & System.IO.FileAttributes.Temporary) == System.IO.FileAttributes.Temporary)
                //    {
                //        tmp_firstCard = fsi[x].FullName;

                //        try
                //        {
                //            Directory.CreateDirectory(firstCard + "\\writable");
                //            Directory.Delete(firstCard + "\\writable");
                //        }
                //        catch (Exception)
                //        {
                //            tmp_firstCard = "";
                //            continue;
                //        }

                //        break;
                //    }
                //}
                #endregion


                storage_card = "\\Storage Card";

                string tmp_first_card = GetStorageCardName(5);

                if (tmp_first_card.Length == 0)
                {
                    storage_card = "\\Mock Storage Card";

                    if (!Directory.Exists(storage_card))
                        Directory.CreateDirectory(storage_card);
                }
                else
                    storage_card = tmp_first_card;
            }
            else
                storage_card = firstCard;

            #endregion


            //Create the upload folders
            try
            {
                path = storage_card + "\\statslog\\";
                if (!Directory.Exists(path))
                    Directory.CreateDirectory(path);
            
                
                uploadpath = path + "upload\\";
                if (!Directory.Exists(uploadpath))
                    Directory.CreateDirectory(uploadpath);

                suceess = true;
            }
            catch
            {
                //Failed to create upload path directory
            }

            return suceess;
        }



       private string GetStorageCardName(int TIMEOUT_SECONDS)
       {
           int number_of_trials = -1;
           string firstCard = "";
           System.IO.DirectoryInfo di;
           System.IO.FileSystemInfo[] fsi;

           while (number_of_trials < TIMEOUT_SECONDS)
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
                           return firstCard;
                       }
                       catch (Exception)
                       {
                           firstCard = "";
                           //Thread.Sleep(1000);
                           continue;
                       }
                       break;
                   }
               }

               number_of_trials++;
           }

           return firstCard;
       }




        public void Write(String log)
        {
                DateTime now = DateTime.Now;
                TextWriter tw = null;

                string filename = path + UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + now.Hour + ".csv";


                try
                {
                    if ( !File.Exists(filename) )
                    {
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
                               
                               if ( files_sub_folder.Length > 0 )
                                   File.Move(files[i],uploadpath + file_name_ext + "_" + files_sub_folder.Length.ToString() + ".csv");
                               else
                                 File.Move( files[i], uploadpath + mfilename);
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
                catch (Exception e)
                {

                    //Error("Failed to write summary lines to file when invoked in the wc. FileName: " + filename);
                    if (tw != null)
                    {
                        tw.Flush();
                        tw.Close();
                    }
                }
        }


        public bool Dispose()
        {
            string mfilename = "";
            string file_name_prefix = "";
            string[] files_sub_folder = null;
            bool success = false;


            // when closing, move all the files corresponding to previous hours
            files = Directory.GetFiles(path, UPLOAD_FILE + "*");


            if (files.Length > 0)
            {
                for (int i = 0; i < files.Length; i++)
                {
                    mfilename = files[i].Substring(path.Length);

                    if (!File.Exists(uploadpath + mfilename))
                    {
                        try
                        {
                            File.Move(files[i], uploadpath + mfilename);
                            success = true;
                        }
                        catch
                        {
                            //Error("Failed to move previous files when invoked in the wc. FileName: " + mfilename );  
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

                            success = true;
                        }
                        catch
                        { //Error("Failed to move previous files when invoked in the wc. FileName: " + mfilename );
                        }
                    }
                }
            }
            else
                success = true; //no files need to be moved

            return success;
        }



        //public void Dispose()
        //{

        //    DateTime now = DateTime.Now;
        //    String filename = UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + now.Hour + ".csv";

        //    now = now.Subtract(new TimeSpan(1, 0, 0));
        //    String prevhourfilename = UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + (now.Hour - 1) + ".csv";


        //    try
        //    {
        //        if (File.Exists(path + filename))
        //            if (!File.Exists(uploadpath + filename))
        //                File.Move(path + filename, uploadpath + filename);
        //            else
        //                AppendLinesToFile(path + filename, uploadpath + filename);


        //        if (File.Exists(path + prevhourfilename))
        //            if (!File.Exists(uploadpath + prevhourfilename))
        //                File.Move(path + prevhourfilename, uploadpath + prevhourfilename);
        //            else
        //                AppendLinesToFile(path + prevhourfilename, uploadpath + prevhourfilename);
        //    }
        //    catch
        //    { 
        //        //Failed to dispose CustomSynchronizedLogger Class
        //    }

        //}



        //private void AppendLinesToFile(string source_file, string destination_file)
        //{

        //    try
        //    {

        //        TextReader tr = new StreamReader(source_file);
        //        String line = "";
        //        ArrayList _Lines = null;

        //        while ((line = tr.ReadLine()) != null)
        //        {
        //            _Lines.Add(line);
        //        }
        //        tr.Close();


        //        if ( _Lines != null )
        //        {
        //            TextWriter tw = new StreamWriter(destination_file, true);
        //            for (int i = 0; i < _Lines.Count; i++)
        //              tw.WriteLine(_Lines[i]);
                    
        //            tw.Flush();
        //            tw.Close();
        //        }


        //    }
        //    catch
        //    {
        //        // Failed to append lines to destination files
        //    }

        //}



        //public void Flush()
        //{
            
        //    DateTime now = DateTime.Now;
        //    TextWriter tw = null;
        //    String filename = UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + now.Hour + ".csv";


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

        //                if (!File.Exists(uploadpath + mfilename))
        //                    File.Move(files[i], uploadpath + mfilename);
        //                else
        //                    AppendLinesToFile(files[i], uploadpath + mfilename);
        //            }

        //        }

        //    }
        //    catch (Exception e)
        //    {
        //        // Failed to flush file of customSynchronizedLogger Class
        //        if (tw != null)
        //        {
        //            tw.Flush();
        //            tw.Close();
        //        }
        //    }

        //}


    }
  }


