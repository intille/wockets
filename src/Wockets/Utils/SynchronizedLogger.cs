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
        public static ArrayList _Lines = null;
        private const String UPLOAD_FILE="upload_file_";
        private static String lastFile = "";
        private static ArrayList _NewLines = null;
        private static string[] files;
        

        static SynchronizedLogger()
        {            
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

            path += "\\statslog\\";
            
            //uploadpath += "\\statslog\\upload\\";
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
            _Lines = new ArrayList();

        }


        public static void Remove(ArrayList toRemove)
        {

            try
            {
                    //if (_NewLines != null){if (_NewLines.Count > 0){

                        DateTime now = DateTime.Now;
                        String filename = UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + now.Hour + ".csv";
                        TextWriter tw = new StreamWriter(uploadpath + filename);
                        
                        for (int i = 0; (i < _NewLines.Count); i++)
                            tw.WriteLine(_NewLines[i]);
                        tw.Flush();
                        tw.Close();

                    //}}
            }
            catch
            {
                return;
            }

            for (int i = 0; (i < files.Length); i++)
                File.Delete(files[i]);                        
        }


        public static void Load()
        {

            files = Directory.GetFiles(uploadpath);
            _Lines.Clear();


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

        public static void Write(String log)
        {

            
            try
            {
                DateTime now = DateTime.Now;
                //String filename= uploadpath+UPLOAD_FILE+now.Day+"-"+now.Hour+".csv";

                String filename = path + UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + now.Hour + ".csv";
                if (!File.Exists(filename))
                {
                    if (lastFile != "")
                        File.Move(path + lastFile, uploadpath + lastFile);
                    File.Create(filename);
                    lastFile = UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + now.Hour + ".csv";
                }
                
                TextWriter tw = new StreamWriter(filename, true);
                tw.WriteLine(log);
                tw.Flush();
                tw.Close();
                
            }
            catch
            {
            }
            
        }

        public static void Dispose()
        {
             DateTime now = DateTime.Now;
             //String filename= uploadpath+UPLOAD_FILE+now.Day+"-"+now.Hour+".csv";            
             String filename = path + UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + now.Hour + ".csv";    
             
             now=now.Subtract(new TimeSpan(1,0,0));
             //String prevhourfilename= uploadpath+UPLOAD_FILE+now.Day+"-"+now.Hour-1 +".csv";  
             String prevhourfilename = path + UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + (now.Hour - 1) + ".csv"; 

            if (File.Exists(filename))             
                 File.Move(path + filename, uploadpath + filename);

             if (File.Exists(prevhourfilename))
                 File.Move(path + prevhourfilename, uploadpath + prevhourfilename);             
                
        }

        public static void Flush()
        {
            
            try
            {
                //TextWriter tw = new StreamWriter(path, true);
                
                DateTime now = DateTime.Now;
                //String filename= uploadpath+UPLOAD_FILE+now.Day+"-"+now.Hour+".csv";
                String filename = path + UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + now.Hour + ".csv";
                if (!File.Exists(filename))
                {
                    if (lastFile != "")
                        File.Move(path + lastFile, uploadpath + lastFile);
                    File.Create(filename);
                    lastFile = UPLOAD_FILE + now.ToString("yyyy-MM-dd") + "_" + now.Hour + ".csv";
                }

                TextWriter tw = new StreamWriter(filename, true);
                for (int i = 0; (i < _Lines.Count); i++)
                    tw.WriteLine(_Lines[i]);

                tw.Flush();
                tw.Close();
            }
            catch
            {
            }            

        }
    }
}
