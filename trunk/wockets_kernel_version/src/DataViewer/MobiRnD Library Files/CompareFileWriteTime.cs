using System;
using System.Collections.Generic;
using System.Text;

using System.IO;

namespace MobiRnD_RDT.Utilities
{
    public class CompareFileWriteTime : IComparer<string>
    {
        public int Compare(string file1, string file2)
        {
            FileInfo fi1 = new FileInfo(file1);
            FileInfo fi2 = new FileInfo(file2);

            return DateTime.Compare(fi1.LastWriteTime,fi2.LastWriteTime);
        }           

    }
}
