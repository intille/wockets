// 32feet.NET
//
// InTheHand.Win32.Registry
// 
// Copyright (c) 2003-2006 In The Hand Ltd
//

using System;
using System.ComponentModel;
using System.Collections;
using System.Runtime.InteropServices;

#if V1 && WinCE

namespace Microsoft.Win32
{
	#region Registry
	
    internal sealed class Registry
	{
		private Registry(){}

		public static readonly RegistryKey LocalMachine = new RegistryKey(0x80000002, "HKEY_LOCAL_MACHINE", true, true);
		
		public static readonly RegistryKey CurrentUser = new RegistryKey(0x80000001, "HKEY_CURRENT_USER", true, true);
		
		/*public static readonly RegistryKey ClassesRoot = new RegistryKey(0x80000000, "HKEY_CLASSES_ROOT", true, true);
		
		public static readonly RegistryKey Users = new RegistryKey(0x80000003, "HKEY_USERS", true, true);*/
	}
	#endregion

	#region Registry Key
	
    internal sealed class RegistryKey : MarshalByRefObject, IDisposable
	{
		//hkey - handle to a registry key
		private uint handle;
		//full name of key
		private string name;
		//was key opened as writable
		private bool writable;
		//is root key
		private bool isroot;

		//error code when all items have been enumerated
		private const int ERROR_NO_MORE_ITEMS = 259;

		#region Constructor
		internal RegistryKey(uint handle, string name, bool writable, bool isroot)
		{
            this.handle = handle;
            this.name = name;
            this.writable = writable;
			this.isroot = isroot;
		}
		#endregion


		#region Name
		
        public string Name
		{
			get
			{
                return this.name;
			}
		}
		#endregion

		#region To String
		
        public override string ToString()
		{
			if(CheckHKey())
			{
                return this.name + " [0x" + this.handle.ToString("X") + "]";
			}
			else
			{
				throw new ObjectDisposedException("The RegistryKey being manipulated is closed (closed keys cannot be accessed).");
			}
		}
		#endregion


		#region Flush
		
        public void Flush()
		{
			//flush changes to memory
            int result = RegFlushKey(this.handle);
		}
		#endregion

		#region Close
		
        public void Close()
		{
            if (this.isroot)
			{
				//we do not close root keys - because they can not be reopened
				//close will fail silently - no exception is raised
			}
			else
			{
				//ignore if already closed
				if(CheckHKey())
				{
					//close the key
                    int result = RegCloseKey(this.handle);

					if(result==0)
					{
						//set handle to invalid value
                        this.handle = 0;
					}
					else
					{
						//error occured
						throw new ExternalException("Error closing RegistryKey");
					}
				}
			}
		}
		#endregion


		#region Create SubKey
		
        public RegistryKey CreateSubKey(string subkey)
		{
			return CreateSubKey(subkey, false);
		}
		
        public RegistryKey CreateSubKey(string subkey, bool createVolatile)
		{
			//check handle is valid
			if(CheckHKey())
			{
				//check subkey is not null
				if(subkey!=null)
				{
					//check subkey length
					if(subkey.Length < 256)
					{
						//handle to new registry key
						uint newhandle = 0;

						//key disposition - did this create a new key or open an existing key
						KeyDisposition kdisp = 0;

						//options
						RegOptions options = 0;
						if(createVolatile)
						{
							options = RegOptions.Volatile;
						}

						//create new key
                        int result = RegCreateKeyEx(this.handle, subkey, 0, null, options, 0, IntPtr.Zero, ref newhandle, ref kdisp);

						if(result==0)
						{
							//success return the new key
                            return new RegistryKey(newhandle, this.name + "\\" + subkey, true, false);
						}
						else
						{
							throw new ExternalException("An error occured creating the registry key.");
						}
					}
					else
					{
						//name is more than 255 chars
						throw new ArgumentException("The length of the specified subkey is longer than the maximum length allowed (255 characters).");
					}
				}
				else
				{
					throw new ArgumentNullException("The specified subkey is null.");
				}
			}
			else
			{
				//registry key is closed
				throw new ObjectDisposedException("The RegistryKey on which this method is being invoked is closed (closed keys cannot be accessed).");
			}
		}
		#endregion

		#region Open SubKey
		
        public RegistryKey OpenSubKey(string name)
		{
			return OpenSubKey(name, false);
		}
		
        public RegistryKey OpenSubKey(string name, bool writable)
		{
			//check handle is valid
			if(CheckHKey())
			{
				//check name is not null
				if(name!=null)
				{
					//check length
					if(name.Length < 256)
					{
						//handle to receive new key
						uint newhandle = 0;

                        int result = RegOpenKeyEx(this.handle, name, 0, 0, ref newhandle);

						if(result==0)
						{
                            return new RegistryKey(newhandle, this.name + "\\" + name, writable, false);
						}
						else
						{
							//desktop model returns null of key not found
							return null;
							//throw new ExternalException("An error occured retrieving the registry key");
						}
					}
					else
					{
						throw new ArgumentException("The length of the specified subkey is longer than the maximum length allowed (255 characters).");
					}
				}
				else
				{
					throw new ArgumentNullException("name is null.");
				}
			}
			else
			{
				throw new ObjectDisposedException("The RegistryKey being manipulated is closed (closed keys cannot be accessed).");
			}
		}
		#endregion

		#region Delete SubKey
		
        public void DeleteSubKey(string subkey)
		{
			DeleteSubKey(subkey, true);
		}
		
        public void DeleteSubKey(string subkey, bool throwOnMissingSubKey)
		{
			if(subkey==null || subkey=="")
			{
				throw new ArgumentNullException("The subkey is null");
			}
			else
			{
				if(CheckHKey())
				{
					//delete the subkey
                    int result = RegDeleteKey(this.handle, subkey);

					//if operation failed
					if(result != 0)
					{
						//only throw if flag was set
						if(throwOnMissingSubKey)
						{
							throw new ArgumentException("The specified subkey is not a valid reference to a registry key");
						}
					}
				}
				else
				{
					//key is closed
					throw new ObjectDisposedException("The RegistryKey on which this method is being invoked is closed (closed keys cannot be accessed).");
				}
			}
		}
		#endregion

		#region Delete SubKey Tree
		
        public void DeleteSubKeyTree(string subkey)
		{
			//call delete subkey - this will delete all sub keys autmoatically
			DeleteSubKey(subkey, true);
		}
		#endregion

		#region Get SubKey Names
		
        public string[] GetSubKeyNames()
		{
			if(CheckHKey())
			{
				//error/success returned by RegKeyEnumEx
				int result = 0;
				//store the names
				System.Collections.ArrayList subkeynames = new System.Collections.ArrayList();
				int index = 0;

				//buffer to store the name
				char[] buffer = new char[256];
				int keynamelen = buffer.Length;

				//enumerate sub keys
                result = RegEnumKeyEx(this.handle, index, buffer, ref keynamelen, 0, null, 0, 0);
				
				//while there are more key names available
				while(result != ERROR_NO_MORE_ITEMS)
				{
					//add the name to the arraylist
					subkeynames.Add(new string(buffer, 0, keynamelen));

					//increment index
					index++;

					//reset length available to max
					keynamelen = buffer.Length;

					//retrieve next key name
                    result = RegEnumKeyEx(this.handle, index, buffer, ref keynamelen, 0, null, 0, 0);
				}

				//sort the results
				subkeynames.Sort();
				
				//return a fixed size string array
				return (string[])subkeynames.ToArray(typeof(string));
			}
			else
			{
				throw new ObjectDisposedException("The RegistryKey being manipulated is closed (closed keys cannot be accessed).");
			}
		}
		#endregion

		#region SubKey Count
		
        public int SubKeyCount
		{
			get
			{
				//check handle
				if(CheckHKey())
				{
					int subkeycount;
					int valuescount;
					int maxsubkeylen;
					int maxsubkeyclasslen;
					int maxvalnamelen;
					int maxvallen;
					char[] name = new char[256];
					int namelen = name.Length;

                    if (RegQueryInfoKey(this.handle, name, ref namelen, 0, out subkeycount, out maxsubkeylen, out maxsubkeyclasslen, out valuescount, out maxvalnamelen, out maxvallen, 0, 0) == 0)
					{
						return subkeycount;
					}
					else
					{
						throw new ExternalException("Error retrieving registry properties");
					}
				}
				else
				{
					throw new ObjectDisposedException("The RegistryKey being manipulated is closed (closed keys cannot be accessed).");
				}
			}
		}
		#endregion


		#region Get Value
		
        public object GetValue(string name)
		{
			return GetValue(name, null);
		}
		
        public object GetValue(string name, object defaultValue)
		{
			if(CheckHKey())
			{
				RegistryValueKind kt = 0;
				//support up to 256 characters (512 bytes)
				byte[] buffer;

				//pass in buffer size
				int size = 0;

				//determine validity and get required buffer size
                int result = RegQueryValueEx(this.handle, name, 0, ref kt, null, ref size);

				//catch value name not valid
				if(result==87)
				{
					return defaultValue;
				}

				//call api again with valid buffer size
				buffer = new byte[size];
                result = RegQueryValueEx(this.handle, name, 0, ref kt, buffer, ref size);

				//return appropriate type of value
				switch(kt)
				{
					case RegistryValueKind.Binary:
						//return binary data (byte[])
						return buffer;

					case RegistryValueKind.DWord:
						//updated return value as Int32
						return System.BitConverter.ToInt32(buffer, 0);

					case RegistryValueKind.ExpandString:
					case RegistryValueKind.String:
						//return value as a string (trailing null removed)
						string val = System.Text.Encoding.Unicode.GetString(buffer, 0, size);
						return val.Substring(0, val.IndexOf('\0'));

					case RegistryValueKind.MultiString:
						//get string of value
						string raw = System.Text.Encoding.Unicode.GetString(buffer, 0, size);
						//multistring ends with double nulls
						raw = raw.Substring(0, raw.IndexOf("\0\0"));
						//return array of substrings between single nulls
						return raw.Split('\0');
					default:
						return defaultValue;
				}
	
			}
			else
			{
				throw new ObjectDisposedException("The RegistryKey being manipulated is closed (closed keys cannot be accessed).");
			}
		}
		#endregion

		#region Get Value Kind
		
        public RegistryValueKind GetValueKind(string name)
		{
			if(CheckHKey())
			{

				RegistryValueKind kt = RegistryValueKind.Unknown;

				//pass in buffer size
				int size = 0;

				//determine validity and get required buffer size
                int result = RegQueryValueEx(this.handle, name, 0, ref kt, null, ref size);

				//catch value name not valid
				if(result != 0)
				{
					throw new Win32Exception(Marshal.GetLastWin32Error(), "Error retrieving value type");
				}
				else
				{
					return kt;
				}
			}
			else
			{
				throw new ObjectDisposedException("The RegistryKey being manipulated is closed (closed keys cannot be accessed).");
			}
		}
		#endregion

		#region Set Value
		
        public void SetValue(string name, object value)
		{
            if (this.writable)
			{
				if(CheckHKey())
				{
					RegistryValueKind type = 0;
					byte[] data;

					switch(value.GetType().ToString())
					{
						case "System.String":
							type = RegistryValueKind.String;
							data = System.Text.Encoding.Unicode.GetBytes((string)value + '\0');
							break;
						case "System.String[]":
							System.Text.StringBuilder sb = new System.Text.StringBuilder();
							foreach (string str in (string[])value)
								sb.Append(str + '\0');
							sb.Append('\0'); // terminated by two null characters
							type = RegistryValueKind.MultiString;
							data = System.Text.Encoding.Unicode.GetBytes(sb.ToString());
							break;
						case "System.Byte[]":
							type = RegistryValueKind.Binary;
							data = (byte[])value;
							break;
						case "System.Int32":
							type = RegistryValueKind.DWord;
							data = BitConverter.GetBytes((int)value);
							break;
						case "System.UInt32":
							type = RegistryValueKind.DWord;
							data = BitConverter.GetBytes((uint)value);
							break;
						default:
							throw new ArgumentException("value is not a supported type");
					}

					int size = data.Length;
                    int result = RegSetValueEx(this.handle, name, 0, type, data, size);


					if(result!=0)
					{
						throw new ExternalException("Error writing to the RegistryKey");
					}
				}
				else
				{
					throw new ObjectDisposedException("The RegistryKey being manipulated is closed (closed keys cannot be accessed).");
				}
			}
			else
			{
				throw new UnauthorizedAccessException("Cannot set value on RegistryKey which was opened as ReadOnly");
			}
		}

        public void SetValue(string name, object value, RegistryValueKind valueKind)
		{
            if (this.writable)
			{
				if(CheckHKey())
				{
					byte[] data;

					switch(valueKind)
					{
						case RegistryValueKind.String:
							data = System.Text.Encoding.Unicode.GetBytes((string)value + '\0');
							break;
						case RegistryValueKind.MultiString:
							System.Text.StringBuilder sb = new System.Text.StringBuilder();
							
							foreach (string str in (string[])value)
								sb.Append(str + '\0');
							sb.Append('\0'); // terminated by two null characters
							data = System.Text.Encoding.Unicode.GetBytes(sb.ToString());
							break;
						case RegistryValueKind.Binary:
							data = (byte[])value;
							break;
						case RegistryValueKind.DWord:
							if(value is UInt32)
							{
								data = BitConverter.GetBytes((uint)value);
							}
							else
							{
								data = BitConverter.GetBytes(Convert.ToInt32(value));
							}
							break;

						default:
							SetValue(name, value);
							return;
					}

					int size = data.Length;
                    int result = RegSetValueEx(this.handle, name, 0, valueKind, data, size);


					if(result!=0)
					{
						throw new Win32Exception(Marshal.GetLastWin32Error(), "Error writing to the RegistryKey");
					}
				}
				else
				{
					throw new ObjectDisposedException("The RegistryKey being manipulated is closed (closed keys cannot be accessed).");
				}
			}
			else
			{
				throw new UnauthorizedAccessException("Cannot set value on RegistryKey which was opened as ReadOnly");
			}
		}
		#endregion

		#region Delete Value
		
        public void DeleteValue(string name)
		{
			DeleteValue(name, true);
		}
		
        public void DeleteValue(string name, bool throwOnMissingValue)
		{
            if (this.writable)
			{
				if(CheckHKey())
				{
					if(name!=null)
					{
						//call api function to delete value
                        int result = RegDeleteValue(this.handle, name);

						//check for error in supplied name
						if(result==87)
						{
							//only throw exception if flag is set
							if(throwOnMissingValue)
							{
								//name doesnt exist
								throw new ArgumentException("name is not a valid reference to a value (and throwOnMissingValue is true) or name is null");
							}
						}
					}
					else
					{
						//name is null
						throw new ArgumentException("name is null");
					}
				}
				else
				{
					//handle is closed throw exception
					throw new ObjectDisposedException("The RegistryKey being manipulated is closed (closed keys cannot be accessed).");
				}
			}
			else
			{
				//key is readonly throw exception
				throw new UnauthorizedAccessException("Cannot delete a value from a RegistryKey opened as ReadOnly.");
			}

		}
		#endregion

		#region Get Value Names
		
        public string[] GetValueNames()
		{
			if(CheckHKey())
			{
				int result = 0;
				//store the names
				ArrayList valuenames = new ArrayList();
				int index = 0;
				//buffer to store the name
				char[] buffer = new char[256];
				int valuenamelen = buffer.Length;

				//get first value name
                result = RegEnumValue(this.handle, index, buffer, ref valuenamelen, 0, 0, null, 0);
				
				//enumerate sub keys
				while(result != ERROR_NO_MORE_ITEMS)
				{
					//add the name to the arraylist
					valuenames.Add(new string(buffer, 0, valuenamelen));
					//increment index
					index++;
					//reset length available to max
					valuenamelen = buffer.Length;

					//get next value name
                    result = RegEnumValue(this.handle, index, buffer, ref valuenamelen, 0, 0, null, 0);
				}

				//sort the results
				valuenames.Sort();
				
				//return a fixed size string array
				return (string[])valuenames.ToArray(typeof(string));
			}
			else
			{
				//key is closed
				throw new ObjectDisposedException("The RegistryKey being manipulated is closed (closed keys cannot be accessed).");
			}
		}
		#endregion

		#region Value Count
		
        public int ValueCount
		{
			get
			{
				//check handle
				if(CheckHKey())
				{
					int subkeycount;
					int valuescount;
					int maxsubkeylen;
					int maxsubkeyclasslen;
					int maxvalnamelen;
					int maxvallen;
					char[] name = new char[256];
					int namelen = name.Length;

                    if (RegQueryInfoKey(this.handle, name, ref namelen, 0, out subkeycount, out maxsubkeylen, out maxsubkeyclasslen, out valuescount, out maxvalnamelen, out maxvallen, 0, 0) == 0)
					{
						return valuescount;
					}
					else
					{
						throw new ExternalException("Error retrieving registry properties");
					}
				}
				else
				{
					throw new ObjectDisposedException("The RegistryKey being manipulated is closed (closed keys cannot be accessed).");
				}
			}
		}
		#endregion


		#region Check HKey
		//used to check that the handle is a valid open hkey
		private bool CheckHKey()
		{
            if (this.handle == 0)
			{
				return false;
			}
			else
			{
				return true;
			}
		}
		#endregion

		#region IDisposable Members
		/// <summary>
		/// Free up resources used by the RegistryKey
		/// </summary>
		public void Dispose()
		{
			//close and save out data
			this.Close();
		}
		#endregion


		#region KeyDisposition Enumeration
		// <summary>
		// Key disposition for RegCreateKey(Ex)
		// </summary>
		private enum KeyDisposition : int 
		{
			CreatedNewKey = 1, 
			OpenedExistingKey = 2 
		}
		#endregion	

		#region Reg Options
		[Flags()]
		private enum RegOptions
		{
			NonVolatile = 0,
			Volatile = 1,
			//CreateLink = 2,
			//BackupRestore = 4,
			//OpenLink = 8,
		}
		#endregion

		#region Registry P/Invokes

		//open key
		[DllImport("coredll.dll", EntryPoint="RegOpenKeyEx", SetLastError=true)] 
		private static extern int RegOpenKeyEx(
			uint hKey,
			string lpSubKey,
			int ulOptions,
			int samDesired,
			ref uint phkResult); 

		//create key
		[DllImport("coredll.dll", EntryPoint="RegCreateKeyEx", SetLastError=true)] 
		private static extern int RegCreateKeyEx(
			uint hKey,
			string lpSubKey,
			int lpReserved,
			string lpClass,
			RegOptions dwOptions,
			int samDesired,
			IntPtr lpSecurityAttributes,
			ref uint phkResult, 
			ref KeyDisposition lpdwDisposition); 

		//enumerate keys
		[DllImport("coredll.dll", EntryPoint="RegEnumKeyEx", SetLastError=true)]
		private static extern int RegEnumKeyEx(
			uint hKey,
			int iIndex, 
			char[] sKeyName,
			ref int iKeyNameLen, 
			int iReservedZero,
			byte[] sClassName,
			int iClassNameLenZero, 
			int iFiletimeZero);

		//enumerate values
		[DllImport("coredll.dll", EntryPoint="RegEnumValue", SetLastError=true)]
		private static extern int RegEnumValue(
			uint hKey,
			int iIndex,
			char[] sValueName, 
			ref int iValueNameLen,
			int iReservedZero,
			int iTypeZero, /*should take ref KeyType but we never want to restrict type when enumerating values*/
			byte[] byData,
			int iDataLenZero /*takes ref int but we dont need the value when enumerating the names*/);

		//query key info
		[DllImport("coredll.dll", EntryPoint="RegQueryInfoKey", SetLastError=true)]
		private static extern int RegQueryInfoKey(
			uint hKey,
			char[] lpClass,
			ref int lpcbClass, 
			int reservedZero,
			out int cSubkey, 
			out int iMaxSubkeyLen,
			out int lpcbMaxSubkeyClassLen,
			out int cValueNames,
			out int iMaxValueNameLen, 
			out int iMaxValueLen,
			int securityDescriptorZero,
			int lastWriteTimeZero);

		//get value
		[DllImport("coredll.dll", EntryPoint="RegQueryValueEx", SetLastError=true)] 
		private static extern int RegQueryValueEx(
			uint hKey,
			string lpValueName,
			int lpReserved, 
			ref RegistryValueKind lpType,
			byte[] lpData,
			ref int lpcbData); 

		//set value
		[DllImport("coredll.dll", EntryPoint="RegSetValueExW", SetLastError=true)] 
		private static extern int RegSetValueEx(
			uint hKey,
			string lpValueName,
			int lpReserved, 
			RegistryValueKind lpType,
			byte[] lpData,
			int lpcbData); 

		//close key
		[DllImport("coredll.dll", EntryPoint="RegCloseKey", SetLastError=true)] 
		private static extern int RegCloseKey(
			uint hKey);

		//delete key
		[DllImport("coredll.dll", EntryPoint="RegDeleteKey", SetLastError=true)]
		private static extern int RegDeleteKey(
			uint hKey,
			string keyName);

		//delete value
		[DllImport("coredll.dll", EntryPoint="RegDeleteValue", SetLastError=true)]
		private static extern int RegDeleteValue(
			uint hKey,
			string valueName);

		//flush key
		[DllImport("coredll.dll", EntryPoint="RegFlushKey", SetLastError=true)]
		private static extern int RegFlushKey(
			uint hKey );


		#endregion
	}
	#endregion

	#region Registry Value Kind Enumeration
	
    internal enum RegistryValueKind : int
	{
        Unknown = 0,
        String = 1,
        ExpandString = 2,
        Binary = 3,	
        DWord = 4,
        MultiString = 7,
	}
	#endregion
}

#endif


