using System;
using System.IO;

namespace HousenCS.IO
{
	/// <summary>
	/// Object for writing ASCII files.
	/// </summary>
	public class FileWriter
	{
		private String fileName = null; 
		private StreamWriter streamWriter = null;
		private FileStream fileStream = null;
		private bool validFile = false;
		private bool isOverwrite = false;  
	
		/// <summary>
		/// Check if a valid file.
		/// </summary>
		/// <returns>Returns true if file is valid</returns>
		public bool IsValidFile()
		{
			return validFile;
		}

		/// <summary>
		/// Initialize with a string.
		/// </summary>
		/// <param name="aFileName">The filename of the file to create</param>
		/// <param name="isOverwrite">If True, file will be overwritten if it exists. Otherwise data will be appended</param>
		public FileWriter(String aFileName, bool isOverwrite)
		{
			this.fileName = aFileName;
			this.isOverwrite = isOverwrite;
		}

		private void SignalError (String s)
		{
			Console.WriteLine("Error in StringWriter: " + s + " for file: " + fileName);
		}

		private void SignalError (Exception e, String s)
		{
			Console.WriteLine("Error in StringWriter: " + e.Message + " " + s + " for file: " + fileName);
		}
    
		private void Warning (String s)
		{
			Console.WriteLine("Warning: " + s + " for file: " + fileName);
		}

		/// <summary>
		/// Flush all the data to the file. 
		/// </summary>
		public void Flush()
		{
			fileStream.Flush();
		}

		/// <summary>
		/// Open the file to write. Print warnings
		/// </summary>
		public void OpenFile ()
		{
			OpenFile (true);
		}
		
		/// <summary>
		/// Open the file to write.
		/// </summary>
		/// <param name="isWarningOn">True if warnings reported to console</param>
		public void OpenFile (bool isWarningOn)
		{
			try
			{
				if (isOverwrite)
					fileStream = new FileStream(fileName,FileMode.Create);
				else
				{
					if (File.Exists(fileName))
					{
						fileStream = new FileStream(fileName,FileMode.Append);
						if (isWarningOn)
							Warning("Appending data");
					}
					else
						fileStream = new FileStream(fileName,FileMode.Create);
				}
			}
			catch (Exception e)
			{
				SignalError(e,"Can't write to file " + fileName);
				return; 
			}

			validFile = true;    
			streamWriter = new StreamWriter(fileStream);
		}
     
		/// <summary>
		/// Close the file after writing.
		/// </summary>
		public void CloseFile ()
		{
			try
			{
				if (streamWriter != null)
					streamWriter.Close();
				else
					SignalError("Could not close " + fileName + " because file not opened!");
			}
			catch (IOException e)
			{
				SignalError(e,"Error closing " + fileName + " file");         
			}
		}
    
		/// <summary>
		/// Write a String to file.
		/// </summary>
		/// <param name="msg">String to write</param>
		public void WriteLine (String msg)
		{
			if (!validFile)
			{
				SignalError("Can't write. File not opened:" + fileName); 
			}

			try 
			{
				if (streamWriter != null)
					streamWriter.WriteLine(msg);
				else
					SignalError("Problem with StreamWriter during write");
			} 
			catch (IOException e)
			{
				SignalError(e,"Error writing a line to " + fileName); 
			}
		}


		/// <summary>
		/// Test method
		/// </summary>
		static void Main()
		{
			String outFile = "\\My Documents\\testOutFile.txt";
        
			Console.WriteLine("Outfile: " + outFile);  
			FileWriter sro = new FileWriter(outFile,true);
			sro.OpenFile();
				       
			for (int i = 0; i < 30; i++)
			{
				sro.WriteLine("This is line " + i);
				Console.WriteLine("Wrote line " + i);
			}
				        
			sro.CloseFile();
		}
	}
}
