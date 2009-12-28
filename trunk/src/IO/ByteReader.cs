using System;
using System.IO;

namespace HousenCS.IO
{
	/// <summary>
	/// Object for reading bytes from files. 
	/// </summary>
	public class ByteReader
	{
		private String fileName = null; 
		private FileStream fileStream = null;
		private bool validFile = false;
		private int position = 0;
		private long totalBytes = 0;
	
		/// <summary>
		/// Check if a valid file.
		/// </summary>
		/// <returns>Returns true if file is valid</returns>
		public bool IsValidFile()
		{
			return validFile;
		}

		/// <summary>
		/// Initialize with a String filename.
		/// </summary>
		/// <param name="aFileName">The file to be read</param>
		public ByteReader(String aFileName)
		{
			this.fileName = aFileName;
		}

		/// <summary>
		/// Make it easier to write informative msgs to Console stdout
		/// </summary>
		/// <param name="s">Additional description as String</param>
		private void SignalError (String s)
		{
			Console.WriteLine("Error in ByteReader: " + s + " for file: " + fileName);
		}

		/// <summary>
		/// Make it easier to write informative msgs to stdout
		/// </summary>
		/// <param name="e">Exception</param>
		/// <param name="s">Additional description as String</param>
		private void SignalError (Exception e, String s)
		{
			Console.WriteLine("Error in ByteReader: " + e.Message + " " + s + " for file: " + fileName);
		}
    
		/// <summary>
		/// Open the file to read
		/// </summary>
		public void OpenFile ()
		{
			try
			{
				fileStream = new FileStream(fileName,FileMode.Open);
				totalBytes = fileStream.Length;
				position = 0;
			}
			catch (Exception e)
			{
				SignalError(e,"Can't find file " + fileName);
				return; 
			}
			validFile = true;
   		}
     
		/// <summary>
		/// Close the file after reading
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
		/// Check if the ByteReader has reached the end of the file.
		/// </summary>
		/// <returns>True if at end of file and no more data available.</returns>
		public bool IsEOF()
		{
			if (position >= totalBytes)
				return true;
			else
				return false;
		}
    
		/// <summary>
		/// Read a single byte from a byte file.
		/// </summary>
		/// <param name="b">A one-valued byte array in which result is returned</param>
		/// <returns>True if got data</returns>
		public bool ReadByte (byte[] b)
		{
			if (!validFile)
			{
				SignalError("Can't read. File not opened:" + fileName); 
				return false;
			}

			if (IsEOF())
			{
				SignalError("Can't read. Ran out of bytes.");
 				return false;
			}

			try 
			{
				if (fileStream != null)
				{
					b[0] = (byte) fileStream.ReadByte();
					position++;
					//Console.WriteLine (position + " of " + totalBytes);
					return true;
				}
				else
				{
					SignalError("Problem with StreamReader during read");
				}
			} 
			catch (IOException e)
			{
				SignalError(e,"Error reading a line from " + fileName); 
			}

			return false;
		}

		private byte[] tb = new byte[1]; //Temp byte
		/// <summary>
		/// Read bytes filling a byte array 
		/// </summary>
		/// <param name="someBytes">A one-valued byte array in which result is returned</param>
		/// <returns>True if got data</returns>
		public bool ReadBytes (byte[] someBytes)
		{
			for (int i = 0; i < someBytes.Length; i++)
			{
				if (ReadByte(tb))
					someBytes[i] = tb[0];
				else
					return false;
			}
			return true;
		}

		/// <summary>
		/// Read a single int value from a byte file.
		/// </summary>
		/// <param name="i">A one-valued int array in which result is stored</param>
		/// <returns>True if got int</returns>
		public bool ReadInt (int[] i)
		{
			byte[] b = new byte[4];
			if (!validFile)
			{
				SignalError("Can't read. File not opened:" + fileName); 
				return false;
			}

			try 
			{
				if (fileStream != null)
				{
					fileStream.Read(b,0,4);
					position += 4;
					i[0] = BitConverter.ToInt32(b,0);
					return true;
				}
				else
					SignalError("Problem with StreamReader during read");
			} 
			catch (IOException e)
			{
				SignalError(e,"Error reading a line from " + fileName); 
				return false;
			}

			return false;
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
			String inFile = "\\My Documents\\testBytes.txt";        
			Console.WriteLine("Infile: " + inFile);  
			ByteReader br = new ByteReader(inFile);
			br.OpenFile();
			bool gotByte = false;
			int[] i = new int[1];
			//byte[] b = new byte[1]; 
				       
			do
			{
				//gotByte = br.ReadByte(b);
				gotByte = br.ReadInt(i);
				if (gotByte)
				{
					Console.Write(i);
				}
				else
					Console.WriteLine("Could not read an int as bytes");
			} while (gotByte);
				        
			br.CloseFile();
		}
	}
}
