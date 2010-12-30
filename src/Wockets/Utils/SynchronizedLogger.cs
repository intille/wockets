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
        private static Semaphore writeLock;
        public static string SL_LOCK = "WocketsSLLock";
        private static String path = "";
        public static ArrayList _Lines;

        static SynchronizedLogger()
        {
            writeLock = new Semaphore(1, 1, SL_LOCK);
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

            try
            {   
                if (!Directory.Exists(path))
                    Directory.CreateDirectory(path);
            }
            catch
            {
            }

            path += "log.csv";
            _Lines = new ArrayList();

        }

        public static void Remove(ArrayList toRemove)
        {
            writeLock.WaitOne();
            try
            {
                TextReader tr = new StreamReader(path);
                String line = "";
                _Lines.Clear();
                while ((line = tr.ReadLine()) != null)
                {
                    if(!toRemove.Contains(line))
                        _Lines.Add(line);
                }
                tr.Close();

                TextWriter tw = new StreamWriter(path);
                for (int i = 0; (i < _Lines.Count); i++)
                    tw.WriteLine(_Lines[i]);
                tw.Flush();
                tw.Close();

            }
            catch
            {
            }
            writeLock.Release();
        }

        public static void Load()
        {
            writeLock.WaitOne();
            try{
                TextReader tr=new StreamReader(path);
                String line="";
                _Lines.Clear();
                while((line=tr.ReadLine())!=null){
                    _Lines.Add(line);
                }
                tr.Close();

            }catch
            {
            }
            writeLock.Release();
        }

        public static void Write(String log)
        {

            writeLock.WaitOne();
            try
            {
                TextWriter tw = new StreamWriter(path, true);
                tw.WriteLine(log);
                tw.Flush();
                tw.Close();
            }
            catch
            {
            }
            writeLock.Release();
        }

        public static void Flush()
        {
            writeLock.WaitOne();
            try
            {
                TextWriter tw = new StreamWriter(path, true);
                for (int i = 0; (i < _Lines.Count); i++)
                    tw.WriteLine(_Lines[i]);
                tw.Flush();
                tw.Close();
            }
            catch
            {
            }
            writeLock.Release();

        }
    }
}
