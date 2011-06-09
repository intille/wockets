using System;
using System.IO;

namespace HousenCS.IO
{
	/// <summary>
	/// An object for writing byte files for efficient storage of data. 
	/// </summary>
	public class ByteWriter
	{
		private String fileName = null; 
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
		/// Create an object to write data as bytes to a file. 
		/// </summary>
		/// <param name="aFileName">The file to save to</param>
		/// <param name="isOverwrite">If True, file will be overwritten if it exists. Otherwise data will be appended</param>
		public ByteWriter(String aFileName, bool isOverwrite)
		{
			this.fileName = aFileName;
			this.isOverwrite = isOverwrite;
		}

		private void SignalError (String s)
		{
			Console.WriteLine("Error in ByteWriter: " + s + " for file: " + fileName);
		}

		private void SignalError (Exception e, String s)
		{
			Console.WriteLine("Error in ByteWriter: " + e.Message + " " + s + " for file: " + fileName);
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
		/// Open the file to write. Print warnings.
		/// </summary>
		public void OpenFile ()
		{
			OpenFile (true);
		}

		/// <summary>
		/// Open the file to write. 
		/// </summary>
		/// <param name="isWarningOn">True if print warnings to the console.</param>
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
		}
     
		/// <summary>
		/// Close the file after writing
		/// </summary>
		public void CloseFile ()
		{
			try
			{
				if (fileStream != null)
					fileStream.Close();
				else
					SignalError("Could not close " + fileName + " because file not opened!");
			}
			catch (IOException e)
			{
				SignalError(e,"Error closing " + fileName + " file");         
			}
		}
    
		/// <summary>
		/// Write an int value as bytes
		/// </summary>
		/// <param name="val">Int value to write as bytes</param>
		public void WriteByte (int val)
		{
			if (!validFile)
			{
				SignalError("Can't write. File not opened:" + fileName); 
			}

			byte[] bytes = BitConverter.GetBytes(val);
				
			try 
			{
				if (fileStream != null)
					fileStream.Write(bytes,0,bytes.Length); 
				else
					SignalError("Problem with ByteWriter during write");
			} 
			catch (IOException e)
			{
				SignalError(e,"Error writing a line to " + fileName); 
			}
		}

		/// <summary>
		/// Write a single byte value 
		/// </summary>
		/// <param name="val">Byte to write</param>
		public void WriteByte (byte val)
		{
			if (!validFile)
			{
				SignalError("Can't write. File not opened:" + fileName); 
			}

			byte[] bytes = new byte[1];
			bytes[0] = val;
				
			try 
			{
				if (fileStream != null)
					fileStream.Write(bytes,0,bytes.Length); 
				else
					SignalError("Problem with ByteWriter during write");
			} 
			catch (IOException e)
			{
				SignalError(e,"Error writing a line to " + fileName); 
			}
		}

		/// <summary>
		/// Write an array of bytes to the file.
		/// </summary>
		/// <param name="someBytes">Array of byte data</param>
		/// <param name="numBytesToWrite">Number of bytes from array to write</param>
		public void WriteBytes (byte[] someBytes, int numBytesToWrite)
		{
			if (!validFile)
			{
				SignalError("Can't write. File not opened:" + fileName); 
			}

			if (numBytesToWrite > someBytes.Length)
			{
				SignalError("More bytesToWrite specified than buffer size"); 
			}

			try 
			{
				if (fileStream != null)
					fileStream.Write(someBytes,0,numBytesToWrite); 
				else
					SignalError("Problem with ByteWriter during writeBytes");
			} 
			catch (IOException e)
			{
				SignalError(e,"Error writing a line to " + fileName); 
			}
		}

		/// <summary>
		/// Write an entire array of bytes as bytes
		/// </summary>
		/// <param name="someBytes">Byte array to save</param>
		public void WriteBytes (byte[] someBytes)
		{
			WriteBytes(someBytes, someBytes.Length);
		}

		/// <summary>
		/// Write a single int value to the file as bytes
		/// </summary>
		/// <param name="val">Int value to write</param>
		public void WriteInt (int val)
		{
			if (!validFile)
			{
				SignalError("Can't write. File not opened:" + fileName); 
			}

			byte[] bytes = BitConverter.GetBytes(val);
				
			try 
			{
				if (fileStream != null)
					fileStream.Write(bytes,0,bytes.Length); 
				else
					SignalError("Problem with ByteWriter during write");
			} 
			catch (IOException e)
			{
				SignalError(e,"Error writing a line to " + fileName); 
			}
		}

		/// <summary>
		/// Write an int as a short int (2 bytes) to file. Note: only works for int values up to 2 bytes large.
		/// </summary>
		/// <param name="val">Int to write</param>
		public void WriteSInt (int val)
		{
			if (!validFile)
			{
				SignalError("Can't write. File not opened:" + fileName); 
			}

			byte[] bytes = BitConverter.GetBytes(val);
				
			try 
			{
				if (fileStream != null)
					fileStream.Write(bytes,0,2); 
				else
					SignalError("Problem with ByteWriter during write SInt");
			} 
			catch (IOException e)
			{
				SignalError(e,"Error writing a line to " + fileName); 
			}
		}

		/// <summary>
		/// Write a single char to file as byte
		/// </summary>
		/// <param name="val">Char to write as byte</param>
		public void writeChar (char val)
		{
			if (!validFile)
			{
				SignalError("Can't write. File not opened:" + fileName); 
			}

			byte[] bytes = BitConverter.GetBytes(val);
				
			try 
			{
				if (fileStream != null)
					fileStream.Write(bytes,0,bytes.Length); 
				else
					SignalError("Problem with ByteWriter during write char");
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
			String outFile = "\\My Documents\\testBytes.txt";
        
			Console.WriteLine("Outfile: " + outFile);  
			ByteWriter bw = new ByteWriter(outFile,true);
			bw.OpenFile();
				       
			for (int i = 0; i < 30; i++)
			{
				bw.WriteInt(i);
				Console.WriteLine("Wrote value: " + i);
			}	        
			bw.CloseFile();
		}
	}
}