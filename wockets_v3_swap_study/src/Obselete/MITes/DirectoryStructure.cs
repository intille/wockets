using System;
using System.Collections;
using System.IO;

namespace HousenCS.MITes
{
	/// <summary>
	/// Summary description for DirectoryStructure.
	/// </summary>
	public class DirectoryStructure
	{
		
		/// <summary>
		/// The root directory of the file saving
		/// </summary>
		public static string Root = "C:\\Handlense\\Data\\";


        /// <summary>
        /// returns the directory of the executable
        /// </summary>
        /// <returns></returns>
        public static string ExecutionDirectory()
        {
           
#if (PocketPC)
            string exeDir = Path.GetDirectoryName(System.Reflection.Assembly.GetExecutingAssembly().GetModules()[0].FullyQualifiedName);
#else

            string exeDir = System.Reflection.Assembly.GetCallingAssembly().Location;
#endif
            return exeDir.Substring(0, exeDir.LastIndexOf('\\'));
            //return System.Reflection.Assembly.GetCallingAssembly().Location;
        }

		/// <summary>
		/// Returns the fully qualified directory 
		/// currently in use. It also ensures that the 
		/// directory exists,etc.
		/// </summary>
		/// <returns></returns>
		public static string DirectoryToUse()
		{
			
			DateTime time = DateTime.Now;

			//Here I set up the month year day directory: Root\yyyy-MM-dd\hh\
			string path = Root + time.ToString("yyyy-MM-dd")+"\\"+((time.ToString("HH")).TrimStart(new char[]{'0'}))+"\\" ;
			
			
			if(!Directory.Exists(path))
				Directory.CreateDirectory(path);


			return path; 

		}

		public static string DirectoryToUse(string root)
		{
			
			DateTime time = DateTime.Now;

			//Here I set up the month year day directory: Root\yyyy-MM-dd\hh\
            string path = root + time.ToString("yyyy-MM-dd") + "\\" + (time.ToString("HH").TrimStart(new char[] { '0' })) + "\\";
			
			
			if(!Directory.Exists(path))
				Directory.CreateDirectory(path);


			return path; 

		}

		/// <summary>
		/// Returns the fully qualified directory 
		/// currently in use. It also ensures that the 
		/// directory exists,etc.
		/// </summary>
		/// <returns></returns>
		public static string DirectoryToUse(string root, DateTime time)
		{
			
			

			//Here I set up the month year day directory: Root\yyyy-MM-dd\hh\
            string path = root + time.ToString("yyyy-MM-dd") + "\\" + (time.ToString("HH").TrimStart(new char[] { '0' }) )+ "\\";
			
			
			if(!Directory.Exists(path))
				Directory.CreateDirectory(path);


			return path; 

		}

		public static string DayDirectoryToUse()
		{
			DateTime time = DateTime.Now;

			//Here I set up the month year day directory: Root\yyyy-MM-dd\hh\
			string path = Root + time.ToString("yyyy-MM-dd");
			
			
			if(!Directory.Exists(path))
				Directory.CreateDirectory(path);


			return path; 

		}

        public static string DayDirectoryToUse(string rootDir)
        {
            DateTime time = DateTime.Now;

            //Here I set up the month year day directory: Root\yyyy-MM-dd\hh\
            string path = rootDir + time.ToString("yyyy-MM-dd");

            if (!Directory.Exists(path))
                Directory.CreateDirectory(path);


            return path;

        }

		public static string DayDirectoryToUse(string root, DateTime time)
		{
			
			

			//Here I set up the month year day directory: Root\yyyy-MM-dd\hh\
			string path = root + time.ToString("yyyy-MM-dd");
			
			
			if(!Directory.Exists(path))
				Directory.CreateDirectory(path);


			return path; 

		}

		

		
		public static string GetDate()
		{
			DateTime dt = DateTime.Now;
			return (dt.Year + "-" + dt.Month + "-" + dt.Day + "-" + dt.Hour + "-" + dt.Minute + "-" + dt.Second + "-" + dt.Millisecond);
			
		}

		public static string GetDate(DateTime dt)
		{
			
			return (dt.Year + "-" + dt.Month + "-" + dt.Day + "-" + dt.Hour + "-" + dt.Minute + "-" + dt.Second + "-" + dt.Millisecond);
			
		}

		public static string GetDayFolder()
		{
			DateTime dt = DateTime.Now;
			return (dt.ToString("yyyy-MM-dd"));
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns>Either a sorted array of DayFolderNodes or Null if neither were found</returns>
		public static DayFolderNode[] GetDirectoryStructure(string directory)
		{
			//Get all the data files
			try 
			{
				//Get the directory info based on the path
				DirectoryInfo di = new DirectoryInfo(directory);
				
				//Find any data files in the specified directory
				FileSystemInfo[] fia = di.GetFileSystemInfos(DayFolderNode.DAY_FOLDER_SP );

				if(fia == null || fia.Length ==0)
				{
						//The passed directory does not suit our needs
						return null;

				}
				else
				{

					return GetDayFolderInformation(fia);
				}
			}
			catch
			{
				return null;
			}

		}


		/// <summary>
		/// 
		/// </summary>
		/// <returns>Either a sorted array of DayFolderNodes or Null if neither were found</returns>
		public static DayFolderNode[] GetDirectoryStructureForDay(string day)
		{
			//Get all the data files
			try 
			{
				//Get the directory info based on the path
				DirectoryInfo di = new DirectoryInfo(day);
				
			
				FileSystemInfo[] fia = new FileSystemInfo[1];
				fia[0] = di;

				if(fia == null || fia.Length ==0)
				{
					//The passed directory does not suit our needs
					return null;

				}
				else
				{

					return GetDayFolderInformation(fia);
				}
			}
			catch
			{
				return null;
			}

		}

		public static DayFolderNode[] GetDirectoryStructureForDay(string day, string fileRegex)
		{
			//Get all the data files
			try 
			{
				//Get the directory info based on the path
				DirectoryInfo di = new DirectoryInfo(day);
				FileSystemInfo[] fia = new FileSystemInfo[1];
				fia[0] = di;
				
				if(fia == null || fia.Length ==0)
				{
					//The passed directory does not suit our needs
					return null;

				}
				else
				{

					return GetDayFolderInformation(fia,fileRegex);
				}
			}
			catch(Exception e)
			{
				Console.Out.WriteLine(e.Message+"\n"+e.StackTrace);
				return null;
			}

		}

		

		/// <summary>
		/// 
		/// </summary>
		/// <returns>Either a sorted array of DayFolderNodes or Null if neither were found</returns>
		public static DayFolderNode[] GetDirectoryStructure(string directory, string fileRegex)
		{
			//Get all the data files
			try 
			{
				//Get the directory info based on the path
				DirectoryInfo di = new DirectoryInfo(directory);
				
				//Find any data files in the specified directory
				FileSystemInfo[] fia = di.GetFileSystemInfos(DayFolderNode.DAY_FOLDER_SP );

				if(fia == null || fia.Length ==0)
				{
					//The passed directory does not suit our needs
					return null;

				}
				else
				{

					return GetDayFolderInformation(fia,fileRegex);
				}
			}
			catch(Exception e)
			{
				Console.Out.WriteLine(e.Message+"\n"+e.StackTrace);
				return null;
			}

		}

		private static DayFolderNode[] GetDayFolderInformation(FileSystemInfo[] fia)
		{
			if(fia == null || fia.Length<1)
				return null;

			System.Collections.ArrayList ret = new System.Collections.ArrayList();
			
			DayFolderNode dfn;
			HourFolderNode[] hours =null;
			
			DateTime dt;

			foreach(FileSystemInfo fsi in fia)
			{

				//fill the info
				dfn=new DayFolderNode();
			
				dfn.folderName = fsi.FullName;
				dfn.dayAsString = fsi.Name;

				
				if(!DirectoryStructure.TimeFromDayFolderName(fsi.Name,out dt))
				{
					return null;
				}

				dfn.startUnixTime = UnixTime.GetUnixTime(dt);
				dfn.endUnixTime = dfn.startUnixTime+UnixTime.MilliInDay-1;

				//Get the hour information
				hours =  DirectoryStructure.GetHourFolderInformation(fsi.FullName,dfn.startUnixTime);
				if(hours==null || hours.Length<1)
					continue;
				
				dfn.hours = hours;

				//add to the list
				ret.Add(dfn);

				hours = null;
				dfn = null;
			}

			if(ret.Count>0)
			{
				//Create the array to return
				return (DayFolderNode[])ret.ToArray(typeof(DayFolderNode));
			}
			else
			{
				return null;
			}
		}


		private static DayFolderNode[] GetDayFolderInformation(FileSystemInfo[] fia,string fileRegex)
		{
			if(fia == null || fia.Length<1)
				return null;

			System.Collections.ArrayList ret = new System.Collections.ArrayList();
			
			DayFolderNode dfn;
			HourFolderNode[] hours =null;
			
			DateTime dt;

			foreach(FileSystemInfo fsi in fia)
			{

				//fill the info
				dfn=new DayFolderNode();
			
				dfn.folderName = fsi.FullName;
				
				if(!DirectoryStructure.TimeFromDayFolderName(fsi.Name,out dt))
				{
					return null;
				}

				dfn.startUnixTime = UnixTime.GetUnixTime(dt);
				dfn.endUnixTime = dfn.startUnixTime+UnixTime.MilliInDay-1;

				//Get the hour information
				hours =  DirectoryStructure.GetHourFolderInformation(fsi.FullName,dfn.startUnixTime,fileRegex);
				if(hours==null || hours.Length<1)
					continue;
				
					dfn.hours = hours;

				//add to the list
				ret.Add(dfn);

				hours = null;
				dfn = null;
			}

			if(ret.Count>0)
			{
				//Create the array to return
				return (DayFolderNode[])ret.ToArray(typeof(DayFolderNode));
			}
			else
			{
				return null;
			}
		}
		
		/// <summary>
		/// This function takes a string that points to a Day folder 'folder' and returns all the hour folders.
		///  The dayStartUnixTime is the UnixTime of the year-month-day 
		/// combination from the Day folder. 
		/// </summary>
		/// <param name="folder"></param>
		/// <param name="dayStartUnixTime"></param>
		/// <returns></returns>
		private static HourFolderNode[] GetHourFolderInformation(string folder, double dayStartUnixTime)
		{
			if(folder == null || folder.Length<1)
				return null;

			
			FileSystemInfo[] fi =null;
			FileSystemInfo[] fia =null;
			DirectoryInfo di=null;
			HourFolderNode[] ret;
			

			//Get the directory info based on the path
			di = new DirectoryInfo(folder);
		
			fi =  di.GetFileSystemInfos(HourFolderNode.HOUR_FOLDER_SP);

			if(fi == null || fi.Length ==0)
			{
				//The  directory does not have hour information
				return null;
			}

			
			Array.Sort(fi,new FileSystemInfoNameComparer());
			
			ret = new HourFolderNode[fi.Length];
			int ind =0;
			foreach(FileSystemInfo fsi in fi )
			{

				//Get the directory info based on the path
				di = new DirectoryInfo(fsi.FullName);
				//Find any data files in the specified directory
				fia = di.GetFileSystemInfos();
				if(fia == null || fia.Length ==0)
				{
					//The passed directory does not suit our needs
					continue;

				}
				
				ret[ind] = new HourFolderNode();
				ret[ind].folderName = fsi.FullName;
				try
				{
					ret[ind].hour = Int32.Parse(fsi.Name);
				}
				catch{}
				ret[ind].startUnixTime = dayStartUnixTime+ (ret[ind].hour*UnixTime.MilliInHour);
				ret[ind].endUnixTime = ret[ind].startUnixTime+ UnixTime.MilliInHour-1;
				ind++;
			}

				
				
			return ret; 

		}


		/// <summary>
		/// This function takes a string that points to a Day folder 'folder' and returns all the hour folders that
		/// have a file in them that matches 'fileRegex'. The dayStartUnixTime is the UnixTime of the year-month-day 
		/// combination from the Day folder. 
		/// </summary>
		/// <param name="folder"></param>
		/// <param name="dayStartUnixTime"></param>
		/// <param name="fileRegex"></param>
		/// <returns></returns>
		private static HourFolderNode[] GetHourFolderInformation(string folder, double dayStartUnixTime, string fileRegex)
		{
			if(folder == null || folder.Length<1)
				return null;

			
			FileSystemInfo[] fi =null;
			FileSystemInfo[] fia =null;
			DirectoryInfo di=null;
			HourFolderNode[] ret;
			

			//Get the directory info based on the path
			di = new DirectoryInfo(folder);
			fi =  di.GetFileSystemInfos(HourFolderNode.HOUR_FOLDER_SP);
			if(fi == null || fi.Length ==0)
			{
				//The  directory does not have hour information
				return null;
			}
			
			ret = new HourFolderNode[fi.Length];
			int ind =0;
			foreach(FileSystemInfo fsi in fi )
			{

				//Get the directory info based on the path
				di = new DirectoryInfo(fsi.FullName);
				//Find any data files in the specified directory
				 fia = di.GetFileSystemInfos(fileRegex );
				if(fia == null || fia.Length ==0)
				{
					//The passed directory does not suit our needs
					continue;

				}
				
				ret[ind] = new HourFolderNode();
				ret[ind].folderName = fsi.FullName;
				try
				{
					ret[ind].hour = Int32.Parse(fsi.Name);
				}
				catch{}
				ret[ind].startUnixTime = dayStartUnixTime+ (ret[ind].hour*UnixTime.MilliInHour);
				ret[ind].endUnixTime = ret[ind].startUnixTime+ UnixTime.MilliInHour-1;
				ind++;
			}

				
				
			return ret; 

		}


		private static bool TimeFromDayFolderName(string Day, out DateTime dt)
		{
			dt = DateTime.UtcNow;

			if(Day == null)
				return false;

			string[] tok = Day.Split(new char[] {'-'});
			if(tok == null || tok.Length!=3)
				return false;
			try
			{
				int year = Int32.Parse(tok[0]);
				int month = Int32.Parse(tok[1]);
				int day = Int32.Parse(tok[2]);

				dt = new DateTime(year,month,day,0,0,0,DateTimeKind.Local);
				return true;
			}
			catch
			{
				return false;
			}
		}

	}


	/// <summary>
	/// This class is a container for information about a folder that has been designated as a 
	/// day. This folder contains hour folders which then contai the actual data. 
	/// </summary>
	public class DayFolderNode
	{
		
		/// <summary>
		/// This is the SearhPattern expression for finding the day folder
		/// </summary>
		public const string DAY_FOLDER_SP=  "????-??-??";


		

		/// <summary>
		/// The fully qualified name that this node contains information about
		/// </summary>
		public string folderName = "None";
		public string dayAsString ="None";

		/// <summary>
		/// This number represents the unix time stamp of the first piece of data in this folder 
		/// </summary>
		public double startUnixTime =0;
		public double endUnixTime =0;


		/// <summary>
		/// A pointer to the hour folders within this day directory
		/// </summary>
		public HourFolderNode[] hours = null;


	}

	public class HourFolderNode
	{
		#region Regular Expressions
		/// <summary>
		/// This is the searchpattern for finding the hour folder
		/// </summary>
		public const string HOUR_FOLDER_SP =  "??";
		#endregion

		/// <summary>
		/// The fully qualified name that this node contains information about
		/// </summary>
		public string folderName = "None";

		/// <summary>
		/// This number represents the unix time stamp of the first piece of data in this folder 
		/// </summary>
		public double startUnixTime =0;
		public double endUnixTime =0;

		/// <summary>
		/// The integer rep of this hour
		/// </summary>
		public int hour =0;

	}


	/// <summary> 
	/// This class is created by Anton Zamov 
	/// For more information about Anton Zamov  
	/// and a lot of other useful examples  
	/// please visit http://zamov.online.fr 
	/// You may use and redistribute this code as 
	/// long as you keep this message intact. 
	/// </summary> 
	public class FileSystemInfoNameComparer: IComparer  
	{ 
		public int Compare (object x, object y)  
		{ 

		
			try
			{
				FileSystemInfo FileX=(FileSystemInfo)x; 
				FileSystemInfo FileY=(FileSystemInfo)y; 

				return FileX.Name.CompareTo(FileY.Name);

			}
			catch
			{
				
				return 0;
			}
		  

             
		
		} 

	} 



}
