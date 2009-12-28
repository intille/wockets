using System;
using System.IO;
using System.Reflection;
using System.Text.RegularExpressions;

namespace HousenCS.IO
{
	/// <summary>
	/// Object for reading ASCII files (e.g. saved with FileWriter).
	/// </summary>
	public class FileReader
	{
		private String fileName = null; 
		private StreamReader streamReader = null;
		private FileStream fileStream = null;
		private bool validFile = false;
		private bool isResource = false;
	
		/// <summary>
		/// Check if a valid file.
		/// </summary>
		/// <returns>Returns true if file is valid</returns>
		public bool IsValidFile()
		{
			return validFile;
		}

		/// <summary>
		/// Initialize with a string
		/// </summary>
		/// <param name="aFileName">String filename</param>
		public FileReader(String aFileName)
		{
			this.fileName = aFileName;
		}

		/// <summary>
		/// Initialize with a string, indicate if a resource or a file
		/// </summary>
		/// <param name="aFileName"></param>
		/// <param name="isResource">True if string is resource name</param>
		public FileReader(String aFileName, bool isResource)
		{
			this.isResource = isResource;
			this.fileName = aFileName;
		}

		private void SignalError (String s)
		{
			Console.WriteLine("Error in StringReader: " + s + " for file: " + fileName);
		}

		private void SignalError (Exception e, String s)
		{
			Console.WriteLine("Error in StringReader: " + e.Message + " " + s + " for file: " + fileName);
		}
    
		/// <summary>
		/// Open the file to read.
		/// </summary>
		public void OpenFile ()
		{
			if (isResource)
			{    
				Assembly assem = System.Reflection.Assembly.GetExecutingAssembly ();
//				FileStream s = null;
//				s = (FileStream) assem.GetManifestResourceStream(fileName);
//				Console.WriteLine ("Stream: " + s);
//				streamReader = new StreamReader(s);
			}
			else
			{
				try
				{
					fileStream = new FileStream(fileName,FileMode.Open);
					streamReader = new StreamReader(fileStream);

				}
				catch (Exception e)
				{
					SignalError(e,"Can't find file " + fileName);
					return; 
				}
			}
			validFile = true;
		}
     
		/// <summary>
		/// Close the file after reading.
		/// </summary>
		public void CloseFile ()
		{
			try
			{
				if (streamReader != null)
					streamReader.Close();
				else
					SignalError("Could not close " + fileName + " because file not opened!");
			}
			catch (IOException e)
			{
				SignalError(e,"Error closing " + fileName + " file");         
			}
		}
    
		/// <summary>
		/// Read a single line from the file as a String
		/// </summary>
		/// <returns>The String line</returns>
		public String ReadLine ()
		{
			if (!validFile)
			{
				SignalError("Can't read. File not opened:" + fileName); 
				return null;
			}

			try 
			{
				if (streamReader != null)
					return streamReader.ReadLine();
				else
					SignalError("Problem with StreamReader during read");
			} 
			catch (IOException e)
			{
				SignalError(e,"Error reading a line from " + fileName); 
				return null;
			}

			return null;
		}

//		private String[] SplitString(String aString)
//		{
//			return (new Regex(" ")).Split(aString);
//		}
    
		/// <summary>
		/// Test method
		/// </summary>
		static void Main()
		{
			String inFile = "\\My Documents\\ingredientHashData.txt";
			String line;
        
			Console.WriteLine("Infile: " + inFile);  
			FileReader sro = new FileReader(inFile);
			sro.OpenFile();
				       
			do
			{
				line = sro.ReadLine();
				if (line != null)
				{
					Console.WriteLine("Orig Line: " + line);
				}
				else
					Console.WriteLine("Could not read a line");
			} while (line != null);
				        
			sro.CloseFile();
		}
	}
}
