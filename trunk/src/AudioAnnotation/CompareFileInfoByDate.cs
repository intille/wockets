using System;
using System.Collections;
using System.IO;


/// <summary>
/// 
/// </summary>
public class CompareFileInfoByDate:IComparer
{
   
		public int Compare(object x, object y)
        {
            FileInfo File1 = default(FileInfo);
            FileInfo File2 = default(FileInfo);

            File1 = (FileInfo)x;
            File2 = (FileInfo)y;

            return DateTime.Compare(File1.LastWriteTime,File2.LastWriteTime);
        }

	
}



class CompareFileInfoByName : IComparer
{
    public int Compare(object x, object y)
    {
        FileInfo file = (FileInfo)x;
        FileInfo file2 = (FileInfo)y;
        return String.Compare(file.FullName, file2.FullName);
    }
}


class CompareFileInfoBySize : IComparer
{
    public int Compare(object x, object y)
    {
        FileInfo file = (FileInfo)x;
        FileInfo file2 = (FileInfo)y;
        return Decimal.Compare(file.Length, file2.Length);
    }
}

