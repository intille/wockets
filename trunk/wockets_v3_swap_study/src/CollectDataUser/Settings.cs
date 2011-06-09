using System;
using System.Linq;
using System.Collections.Generic;
using System.Text;


namespace CollectDataUser
{
    class Settings
    {
        public static bool _Audio = false;
        public static bool _Running = false;
        public static int _PhoneBattry = 73;
        public static DateTime _SessionStart = DateTime.Now;
        public static string _MainWocketsDirectory = "";
        public static string _MemoryCardDirectory = "";
        public static string _RootStorageDirectory = "";
        public static string _DataStorageDirectory = "";
        public static int _InternalStorage = 200;
        public static int _SDStorage = 1000;
        public static int _NewFiles = 200;
        public static DateTime _LastUpload = DateTime.Now;
        public static long _UploadDuration = 1000;
        public static int _NumSuccessfulFiles = 101;
        public static int _NumFailedFiles = 101;
     
    }
}
