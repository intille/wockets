using System;
using System.Collections; //ArrayList
using System.Text; //Encoding
using System.Runtime.InteropServices;//P/Invoke


#region Process class
/// <summary>
/// Class to get list of running processes, access information about a given process, kill a given process, or start a new process
/// </summary>
public class Process
{
    #region FIELDS
    private string _processName;
    private IntPtr _handle;
    private int _threadCount;
    private int _baseAddress;
    #endregion

    #region PROPERTIES
    public int BaseAddress
    {
        get
        {
            return _baseAddress;
        }
    }

    public int ThreadCount
    {
        get
        {
            return _threadCount;
        }
    }

    public IntPtr Handle
    {
        get
        {
            return _handle;
        }
    }

    public string ProcessName
    {
        get
        {
            return _processName;
        }
    }

    public int BaseAddess
    {
        get
        {
            return _baseAddress;
        }
    }
    #endregion

    #region CONSTRUCTORS
    public Process() { }

    private Process(IntPtr id, string procname, int threadcount, int baseaddress)
    {
        _handle = id;
        _processName = procname;
        _threadCount = threadcount;
        _baseAddress = baseaddress;
    }
    #endregion

    #region PUBLIC METHODS
    public override string ToString()
    {
        return _processName;
    }
    
    public void Kill()
    {
        IntPtr hProcess;

        hProcess = OpenProcess(PROCESS_TERMINATE, false, (int)_handle);

        if (hProcess != (IntPtr)INVALID_HANDLE_VALUE)
        {
            bool bRet;
            bRet = TerminateProcess(hProcess, 0);
            CloseHandle(hProcess);
        }


    }


    #region STATIC METHODS
    public static Process[] GetProcesses()
    {
        ArrayList procList = new ArrayList();

        //Added TH32CS_SNAPNOHEAPS, 4/22/08 for WM 5.0 problem
        IntPtr _handle = CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS | TH32CS_SNAPNOHEAPS, 0);

        if ((int)_handle > 0)
        {
            try
            {
                PROCESSENTRY32 peCurrent;
                PROCESSENTRY32 pe32 = new PROCESSENTRY32();
                //Get byte array to pass to the API calls
                byte[] peBytes = pe32.ToByteArray();
                //Get the first process
                int retval = Process32First(_handle, peBytes);

                while (retval == 1)
                {
                    //Convert bytes to the class
                    peCurrent = new PROCESSENTRY32(peBytes);
                    //New instance
                    Process proc = new Process(new IntPtr((int)peCurrent.PID), peCurrent.Name, (int)peCurrent.ThreadCount, (int)peCurrent.BaseAddress);

                    procList.Add(proc);

                    retval = Process32Next(_handle, peBytes);
                }
            }
            catch (Exception ex)
            {
                throw new Exception("Exception: " + ex.Message);
            }

            //Close _handle
            CloseToolhelp32Snapshot(_handle);

            return (Process[])procList.ToArray(typeof(Process));

        }
        else
        {
            throw new Exception("Unable to create snapshot");
        }


    }

    public static bool IsExeRunning(string exeFilename)
    {
        bool isRunning = false;
        
        exeFilename = exeFilename.ToLower();
        Process[] pRunning = Process.GetProcesses();
        for (int i = 0; i < pRunning.Length; i++)
        {
            if (pRunning[i].ToString().ToLower().Equals(exeFilename))
            {
                isRunning = true;
            }
        }


        return isRunning;
    }

    public static bool StartProcess(string pathExecutable, string arguments)
    {
        return CreateProcess(pathExecutable, arguments, IntPtr.Zero, IntPtr.Zero, 0, 0, IntPtr.Zero, IntPtr.Zero, IntPtr.Zero, null);
    }

    public static Process GetProcess(string exeFilename)
    {
        Process foundProcess = null;
        
        exeFilename = exeFilename.ToLower();
        Process[] pRunning = Process.GetProcesses();
        for (int i = 0; i < pRunning.Length; i++)
        {
            if (pRunning[i].ToString().ToLower().Equals(exeFilename))
            {
                foundProcess = pRunning[i];
            }
        }


        return foundProcess;
    }
    #endregion

    #endregion
    
    #region PROCESSENTRY32 implementation

    //		typedef struct tagPROCESSENTRY32 
    //		{ 
    //			DWORD dwSize; 
    //			DWORD cntUsage; 
    //			DWORD th32ProcessID; 
    //			DWORD th32DefaultHeapID; 
    //			DWORD th32ModuleID; 
    //			DWORD cntThreads; 
    //			DWORD th32ParentProcessID; 
    //			LONG pcPriClassBase; 
    //			DWORD dwFlags; 
    //			TCHAR szExeFile[MAX_PATH]; 
    //			DWORD th32MemoryBase;
    //			DWORD th32AccessKey;
    //		} PROCESSENTRY32;

    private class PROCESSENTRY32
    {
        // constants for structure definition
        private const int SizeOffset = 0;
        private const int UsageOffset = 4;
        private const int ProcessIDOffset = 8;
        private const int DefaultHeapIDOffset = 12;
        private const int ModuleIDOffset = 16;
        private const int ThreadsOffset = 20;
        private const int ParentProcessIDOffset = 24;
        private const int PriClassBaseOffset = 28;
        private const int dwFlagsOffset = 32;
        private const int ExeFileOffset = 36;
        private const int MemoryBaseOffset = 556;
        private const int AccessKeyOffset = 560;
        private const int Size = 564;
        private const int MAX_PATH = 260;

        // data members
        public uint dwSize;
        public uint cntUsage;
        public uint th32ProcessID;
        public uint th32DefaultHeapID;
        public uint th32ModuleID;
        public uint cntThreads;
        public uint th32ParentProcessID;
        public long pcPriClassBase;
        public uint dwFlags;
        public string szExeFile;
        public uint th32MemoryBase;
        public uint th32AccessKey;

        //Default constructor
        public PROCESSENTRY32()
        {


        }

        // create a PROCESSENTRY instance based on a byte array		
        public PROCESSENTRY32(byte[] aData)
        {
            dwSize = GetUInt(aData, SizeOffset);
            cntUsage = GetUInt(aData, UsageOffset);
            th32ProcessID = GetUInt(aData, ProcessIDOffset);
            th32DefaultHeapID = GetUInt(aData, DefaultHeapIDOffset);
            th32ModuleID = GetUInt(aData, ModuleIDOffset);
            cntThreads = GetUInt(aData, ThreadsOffset);
            th32ParentProcessID = GetUInt(aData, ParentProcessIDOffset);
            pcPriClassBase = (long)GetUInt(aData, PriClassBaseOffset);
            dwFlags = GetUInt(aData, dwFlagsOffset);
            szExeFile = GetString(aData, ExeFileOffset, MAX_PATH);
            th32MemoryBase = GetUInt(aData, MemoryBaseOffset);
            th32AccessKey = GetUInt(aData, AccessKeyOffset);
        }

        #region Helper conversion functions
        // utility:  get a uint from the byte array
        private static uint GetUInt(byte[] aData, int Offset)
        {
            return BitConverter.ToUInt32(aData, Offset);
        }

        // utility:  set a uint int the byte array
        private static void SetUInt(byte[] aData, int Offset, int Value)
        {
            byte[] buint = BitConverter.GetBytes(Value);
            Buffer.BlockCopy(buint, 0, aData, Offset, buint.Length);
        }

        // utility:  get a ushort from the byte array
        private static ushort GetUShort(byte[] aData, int Offset)
        {
            return BitConverter.ToUInt16(aData, Offset);
        }

        // utility:  set a ushort int the byte array
        private static void SetUShort(byte[] aData, int Offset, int Value)
        {
            byte[] bushort = BitConverter.GetBytes((short)Value);
            Buffer.BlockCopy(bushort, 0, aData, Offset, bushort.Length);
        }

        // utility:  get a unicode string from the byte array
        private static string GetString(byte[] aData, int Offset, int Length)
        {
            String sReturn = Encoding.Unicode.GetString(aData, Offset, Length);
            return sReturn;
        }

        // utility:  set a unicode string in the byte array
        private static void SetString(byte[] aData, int Offset, string Value)
        {
            byte[] arr = Encoding.ASCII.GetBytes(Value);
            Buffer.BlockCopy(arr, 0, aData, Offset, arr.Length);
        }
        #endregion

        // create an initialized data array
        public byte[] ToByteArray()
        {
            byte[] aData;
            aData = new byte[Size];
            //set the Size member
            SetUInt(aData, SizeOffset, Size);
            return aData;
        }

        public string Name
        {
            get
            {
                return szExeFile.Substring(0, szExeFile.IndexOf('\0'));
            }
        }

        public ulong PID
        {
            get
            {
                return th32ProcessID;
            }
        }

        public ulong BaseAddress
        {
            get
            {
                return th32MemoryBase;
            }
        }

        public ulong ThreadCount
        {
            get
            {
                return cntThreads;
            }
        }
    }
    #endregion

    #region PInvoke declarations

    #region GET PROCESSES
    //Added TH32CS_SNAPNOHEAPS, 4/22/08 for WM 5.0 problem
    private const int TH32CS_SNAPNOHEAPS = 0x40000000;
    private const int TH32CS_SNAPPROCESS = 0x00000002;
    [DllImport("toolhelp.dll")]
    public static extern IntPtr CreateToolhelp32Snapshot(uint flags, uint processid);
    [DllImport("toolhelp.dll")]
    public static extern int CloseToolhelp32Snapshot(IntPtr _handle);
    [DllImport("toolhelp.dll")]
    public static extern int Process32First(IntPtr _handle, byte[] pe);
    [DllImport("toolhelp.dll")]
    public static extern int Process32Next(IntPtr _handle, byte[] pe);
    #endregion

    #region KILL PROCESS
    [DllImport("coredll.dll")]
    private static extern IntPtr OpenProcess(int flags, bool fInherit, int PID);

    private const int PROCESS_TERMINATE = 1;
    [DllImport("coredll.dll")]
    private static extern bool TerminateProcess(IntPtr hProcess, uint ExitCode);
    [DllImport("coredll.dll")]
    private static extern bool CloseHandle(IntPtr _handle);
    private const int INVALID_HANDLE_VALUE = -1;
    #endregion

    #region CREATE PROCESS
    [DllImport("coredll", EntryPoint = "CreateProcess", SetLastError = true)]
    private extern static bool CreateProcess(string pszImageName, string pszCmdLine, IntPtr psaProcess, IntPtr psaThread, int fInheritHandles, int fdwCreate, IntPtr pvEnvironment, IntPtr pszCurDir, IntPtr psiStartInfo, ProcessInfo pi);


    private sealed class ProcessInfo
    {
        public IntPtr Process = IntPtr.Zero;
        public IntPtr Thread = IntPtr.Zero;
        public int ProcessID = 0;
        public int ThreadID = 0;
    }
    #endregion

    #endregion
}
#endregion
