using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Utils
{
    public class Storage
    {
        public static string GenerateStoragePath()
        {
            string path = "";

            System.IO.DirectoryInfo di = new System.IO.DirectoryInfo("\\");
            System.IO.FileSystemInfo[] fsi = di.GetFileSystemInfos();
            string firstCard = "";
            //iterate through them
            for (int x = 0; x < fsi.Length; x++)
            {
                //check to see if this is a temporary storage card (e.g. SD card)
                if ((fsi[x].Attributes & System.IO.FileAttributes.Temporary) == System.IO.FileAttributes.Temporary)
                {
                    firstCard = fsi[x].FullName;
                    try
                    {
                        System.IO.Directory.CreateDirectory(firstCard + "\\writable");
                        System.IO.Directory.Delete(firstCard + "\\writable");
                    }
                    catch (Exception)
                    {
                        firstCard = "";
                        continue;
                    }
                    //if so, return the path

                    break;
                }
            }
            DateTime now = DateTime.Now;
            path = firstCard + "\\Wockets\\Session-" + now.Month.ToString("00") + "-" + now.Day.ToString("00") + "-" + now.Year.ToString("0000") + "-" + now.Hour.ToString("00") + "-" + now.Minute.ToString("00") + "-" + now.Second.ToString("00");

            try
            {
                if (!System.IO.Directory.Exists(path))
                    System.IO.Directory.CreateDirectory(path);
                return path;
            }
            catch
            {
                return null;
            }

        }
    }
}
