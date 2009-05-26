using System;
using System.Collections.Generic;
using System.Text;
using System.IO;

namespace WocketsApplication.Utils
{
    public class DirectoryHelper
    {
        public static bool isDirectoryEmpty(string path)
        {
            string[] subDirs = Directory.GetDirectories(path);
            if (0 == subDirs.Length)
            {
                string[] files = Directory.GetFiles(path);
                return (0 == files.Length);
            }
            return false;
        }
    }
}
