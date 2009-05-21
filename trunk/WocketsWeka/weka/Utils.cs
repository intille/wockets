/*
*    Utils.java
*    Copyright (C) 1999-2004 University of Waikato
*
*/
using System;
namespace weka.core
{
	
	/// <summary> Class implementing some simple utility methods.
	/// 
	/// </summary>
	/// <author>  Eibe Frank 
	/// </author>
	/// <author>  Yong Wang 
	/// </author>
	/// <author>  Len Trigg 
	/// </author>
	/// <author>  Julien Prados
	/// </author>
	/// <version>  $Revision: 1.44.2.3 $
	/// </version>
	public sealed class Utils
	{
		
		/// <summary>The natural logarithm of 2. </summary>
		public static double log2_Renamed_Field = System.Math.Log(2);
		
		/// <summary>The small deviation allowed in double comparisons </summary>
		public static double SMALL = 1e-6;
		
		
		/// <summary> Reads properties that inherit from three locations. Properties
		/// are first defined in the system resource location (i.e. in the
		/// CLASSPATH).  These default properties must exist. Properties
		/// defined in the users home directory (optional) override default
		/// settings. Properties defined in the current directory (optional)
		/// override all these settings.
		/// 
		/// </summary>
		/// <param name="resourceName">the location of the resource that should be
		/// loaded.  e.g.: "weka/core/Utils.props". (The use of hardcoded
		/// forward slashes here is OK - see
		/// jdk1.1/docs/guide/misc/resources.html) This routine will also
		/// look for the file (in this case) "Utils.props" in the users home
		/// directory and the current directory.
		/// </param>
		/// <returns> the Properties
		/// </returns>
		/// <exception cref="Exception">if no default properties are defined, or if
		/// an error occurs reading the properties files.  
		/// </exception>
		//UPGRADE_ISSUE: Class hierarchy differences between 'java.util.Properties' and 'System.Collections.Specialized.NameValueCollection' may cause compilation errors. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1186'"
		public static System.Collections.Specialized.NameValueCollection readProperties(System.String resourceName)
		{
			
			//UPGRADE_ISSUE: Class hierarchy differences between 'java.util.Properties' and 'System.Collections.Specialized.NameValueCollection' may cause compilation errors. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1186'"
			//UPGRADE_TODO: Format of property file may need to be changed. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1089'"
			System.Collections.Specialized.NameValueCollection defaultProps = new System.Collections.Specialized.NameValueCollection();
            //try
            //{
            //    // Apparently hardcoded slashes are OK here
            //    // jdk1.1/docs/guide/misc/resources.html
            //    if (defaultProps is weka.core.ProtectedProperties)
            //    {
            //        //UPGRADE_ISSUE: Method 'java.lang.ClassLoader.getSystemResourceAsStream' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javalangClassLoader'"
            //        ((weka.core.ProtectedProperties) defaultProps).load(ClassLoader.getSystemResourceAsStream(resourceName));
            //    }
            //    else
            //    {
            //        //UPGRADE_ISSUE: Method 'java.lang.ClassLoader.getSystemResourceAsStream' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javalangClassLoader'"
            //        ClassLoader.getSystemResourceAsStream(resourceName);
            //        //UPGRADE_TODO: Method 'java.util.Properties.load' was converted to 'System.Collections.Specialized.NameValueCollection' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilPropertiesload_javaioInputStream'"
            //        defaultProps = new System.Collections.Specialized.NameValueCollection(System.Configuration.ConfigurationSettings.AppSettings);
            //    }
            //}
            //catch (System.Exception ex)
            //{
            //    /*      throw new Exception("Problem reading default properties: "
            //    + ex.getMessage()); */
            //    System.Console.Error.WriteLine("Warning, unable to load properties file from " + "system resource (Utils.java)");
            //}
			
            //// Hardcoded slash is OK here
            //// eg: see jdk1.1/docs/guide/misc/resources.html
            //int slInd = resourceName.LastIndexOf('/');
            //if (slInd != - 1)
            //{
            //    resourceName = resourceName.Substring(slInd + 1);
            //}
			
            //// Allow a properties file in the home directory to override
            ////UPGRADE_ISSUE: Class hierarchy differences between 'java.util.Properties' and 'System.Collections.Specialized.NameValueCollection' may cause compilation errors. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1186'"
            ////UPGRADE_TODO: Format of property file may need to be changed. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1089'"
            //System.Collections.Specialized.NameValueCollection userProps = new System.Collections.Specialized.NameValueCollection(defaultProps);
            ////UPGRADE_TODO: Method 'java.lang.System.getProperties' was converted to 'SupportClass.GetProperties' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javalangSystemgetProperties'"
            //System.IO.FileInfo propFile = new System.IO.FileInfo(SupportClass.GetProperties().Get("user.home") + System.IO.Path.DirectorySeparatorChar + resourceName);
            //bool tmpBool;
            //if (System.IO.File.Exists(propFile.FullName))
            //    tmpBool = true;
            //else
            //    tmpBool = System.IO.Directory.Exists(propFile.FullName);
            //if (tmpBool)
            //{
            //    try
            //    {
            //        if (userProps is weka.core.ProtectedProperties)
            //        {
            //            //UPGRADE_TODO: Constructor 'java.io.FileInputStream.FileInputStream' was converted to 'System.IO.FileStream.FileStream' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioFileInputStreamFileInputStream_javaioFile'"
            //            ((weka.core.ProtectedProperties) userProps).load(new System.IO.FileStream(propFile.FullName, System.IO.FileMode.Open, System.IO.FileAccess.Read));
            //        }
            //        else
            //        {
            //            //UPGRADE_TODO: Constructor 'java.io.FileInputStream.FileInputStream' was converted to 'System.IO.FileStream.FileStream' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioFileInputStreamFileInputStream_javaioFile'"
            //            new System.IO.FileStream(propFile.FullName, System.IO.FileMode.Open, System.IO.FileAccess.Read);
            //            //UPGRADE_TODO: Method 'java.util.Properties.load' was converted to 'System.Collections.Specialized.NameValueCollection' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilPropertiesload_javaioInputStream'"
            //            userProps = new System.Collections.Specialized.NameValueCollection(System.Configuration.ConfigurationSettings.AppSettings);
            //        }
            //    }
            //    catch (System.Exception ex)
            //    {
            //        throw new System.Exception("Problem reading user properties: " + propFile);
            //    }
            //}
			
            //// Allow a properties file in the current directory to override
            ////UPGRADE_ISSUE: Class hierarchy differences between 'java.util.Properties' and 'System.Collections.Specialized.NameValueCollection' may cause compilation errors. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1186'"
            ////UPGRADE_TODO: Format of property file may need to be changed. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1089'"
            //System.Collections.Specialized.NameValueCollection localProps = new System.Collections.Specialized.NameValueCollection(userProps);
            //propFile = new System.IO.FileInfo(resourceName);
            //bool tmpBool2;
            //if (System.IO.File.Exists(propFile.FullName))
            //    tmpBool2 = true;
            //else
            //    tmpBool2 = System.IO.Directory.Exists(propFile.FullName);
            //if (tmpBool2)
            //{
            //    try
            //    {
            //        if (localProps is weka.core.ProtectedProperties)
            //        {
            //            //UPGRADE_TODO: Constructor 'java.io.FileInputStream.FileInputStream' was converted to 'System.IO.FileStream.FileStream' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioFileInputStreamFileInputStream_javaioFile'"
            //            ((weka.core.ProtectedProperties) localProps).load(new System.IO.FileStream(propFile.FullName, System.IO.FileMode.Open, System.IO.FileAccess.Read));
            //        }
            //        else
            //        {
            //            //UPGRADE_TODO: Constructor 'java.io.FileInputStream.FileInputStream' was converted to 'System.IO.FileStream.FileStream' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioFileInputStreamFileInputStream_javaioFile'"
            //            new System.IO.FileStream(propFile.FullName, System.IO.FileMode.Open, System.IO.FileAccess.Read);
            //            //UPGRADE_TODO: Method 'java.util.Properties.load' was converted to 'System.Collections.Specialized.NameValueCollection' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilPropertiesload_javaioInputStream'"
            //            localProps = new System.Collections.Specialized.NameValueCollection(System.Configuration.ConfigurationSettings.AppSettings);
            //        }
            //    }
            //    catch (System.Exception ex)
            //    {
            //        throw new System.Exception("Problem reading local properties: " + propFile);
            //    }
            //}
			
			//return localProps;
            return new System.Collections.Specialized.NameValueCollection(); 
		}
		
		/// <summary> Returns the correlation coefficient of two double vectors.
		/// 
		/// </summary>
		/// <param name="y1">double vector 1
		/// </param>
		/// <param name="y2">double vector 2
		/// </param>
		/// <param name="n">the length of two double vectors
		/// </param>
		/// <returns> the correlation coefficient
		/// </returns>
		public static double correlation(double[] y1, double[] y2, int n)
		{
			
			int i;
			double av1 = 0.0, av2 = 0.0, y11 = 0.0, y22 = 0.0, y12 = 0.0, c;
			
			if (n <= 1)
			{
				return 1.0;
			}
			for (i = 0; i < n; i++)
			{
				av1 += y1[i];
				av2 += y2[i];
			}
			av1 /= (double) n;
			av2 /= (double) n;
			for (i = 0; i < n; i++)
			{
				y11 += (y1[i] - av1) * (y1[i] - av1);
				y22 += (y2[i] - av2) * (y2[i] - av2);
				y12 += (y1[i] - av1) * (y2[i] - av2);
			}
			if (y11 * y22 == 0.0)
			{
				c = 1.0;
			}
			else
			{
				c = y12 / System.Math.Sqrt(System.Math.Abs(y11 * y22));
			}
			
			return c;
		}
		
		/// <summary> Removes all occurrences of a string from another string.
		/// 
		/// </summary>
		/// <param name="inString">the string to remove substrings from.
		/// </param>
		/// <param name="substring">the substring to remove.
		/// </param>
		/// <returns> the input string with occurrences of substring removed.
		/// </returns>
		public static System.String removeSubstring(System.String inString, System.String substring)
		{
			
			System.Text.StringBuilder result = new System.Text.StringBuilder();
			int oldLoc = 0, loc = 0;
			//UPGRADE_WARNING: Method 'java.lang.String.indexOf' was converted to 'System.String.IndexOf' which may throw an exception. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1101'"
			while ((loc = inString.IndexOf(substring, oldLoc)) != - 1)
			{
				result.Append(inString.Substring(oldLoc, (loc) - (oldLoc)));
				oldLoc = loc + substring.Length;
			}
			result.Append(inString.Substring(oldLoc));
			return result.ToString();
		}
		
		/// <summary> Replaces with a new string, all occurrences of a string from 
		/// another string.
		/// 
		/// </summary>
		/// <param name="inString">the string to replace substrings in.
		/// </param>
		/// <param name="substring">the substring to replace.
		/// </param>
		/// <param name="replaceString">the replacement substring
		/// </param>
		/// <returns> the input string with occurrences of substring replaced.
		/// </returns>
		public static System.String replaceSubstring(System.String inString, System.String subString, System.String replaceString)
		{
			
			System.Text.StringBuilder result = new System.Text.StringBuilder();
			int oldLoc = 0, loc = 0;
			//UPGRADE_WARNING: Method 'java.lang.String.indexOf' was converted to 'System.String.IndexOf' which may throw an exception. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1101'"
			while ((loc = inString.IndexOf(subString, oldLoc)) != - 1)
			{
				result.Append(inString.Substring(oldLoc, (loc) - (oldLoc)));
				result.Append(replaceString);
				oldLoc = loc + subString.Length;
			}
			result.Append(inString.Substring(oldLoc));
			return result.ToString();
		}
		
		
		/// <summary> Pads a string to a specified length, inserting spaces on the left
		/// as required. If the string is too long, characters are removed (from
		/// the right).
		/// 
		/// </summary>
		/// <param name="inString">the input string
		/// </param>
		/// <param name="length">the desired length of the output string
		/// </param>
		/// <returns> the output string
		/// </returns>
		public static System.String padLeft(System.String inString, int length)
		{
			
			return fixStringLength(inString, length, false);
		}
		
		/// <summary> Pads a string to a specified length, inserting spaces on the right
		/// as required. If the string is too long, characters are removed (from
		/// the right).
		/// 
		/// </summary>
		/// <param name="inString">the input string
		/// </param>
		/// <param name="length">the desired length of the output string
		/// </param>
		/// <returns> the output string
		/// </returns>
		public static System.String padRight(System.String inString, int length)
		{
			
			return fixStringLength(inString, length, true);
		}
		
		/// <summary> Pads a string to a specified length, inserting spaces as
		/// required. If the string is too long, characters are removed (from
		/// the right).
		/// 
		/// </summary>
		/// <param name="inString">the input string
		/// </param>
		/// <param name="length">the desired length of the output string
		/// </param>
		/// <param name="right">true if inserted spaces should be added to the right
		/// </param>
		/// <returns> the output string
		/// </returns>
		private static System.String fixStringLength(System.String inString, int length, bool right)
		{
			
			if (inString.Length < length)
			{
				while (inString.Length < length)
				{
					inString = (right?System.String.Concat(inString, " "):System.String.Concat(" ", inString));
				}
			}
			else if (inString.Length > length)
			{
				inString = inString.Substring(0, (length) - (0));
			}
			return inString;
		}
		
		/// <summary> Rounds a double and converts it into String.
		/// 
		/// </summary>
		/// <param name="value">the double value
		/// </param>
		/// <param name="afterDecimalPoint">the (maximum) number of digits permitted
		/// after the decimal point
		/// </param>
		/// <returns> the double as a formatted string
		/// </returns>
		public static System.String doubleToString(double value_Renamed, int afterDecimalPoint)
		{
			
			System.Text.StringBuilder stringBuffer;
			double temp;
			int dotPosition;
			long precisionValue;
			
			temp = value_Renamed * System.Math.Pow(10.0, afterDecimalPoint);
			if (System.Math.Abs(temp) < System.Int64.MaxValue)
			{
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				precisionValue = (temp > 0)?(long) (temp + 0.5):- (long) (System.Math.Abs(temp) + 0.5);
				if (precisionValue == 0)
				{
					stringBuffer = new System.Text.StringBuilder(System.Convert.ToString(0));
				}
				else
				{
					stringBuffer = new System.Text.StringBuilder(System.Convert.ToString(precisionValue));
				}
				if (afterDecimalPoint == 0)
				{
					return stringBuffer.ToString();
				}
				dotPosition = stringBuffer.Length - afterDecimalPoint;
				while (((precisionValue < 0) && (dotPosition < 1)) || (dotPosition < 0))
				{
					if (precisionValue < 0)
					{
						stringBuffer.Insert(1, "0");
					}
					else
					{
						stringBuffer.Insert(0, "0");
					}
					dotPosition++;
				}
				stringBuffer.Insert(dotPosition, ".");
				if ((precisionValue < 0) && (stringBuffer[1] == '.'))
				{
					stringBuffer.Insert(1, "0");
				}
				else if (stringBuffer[0] == '.')
				{
					stringBuffer.Insert(0, "0");
				}
				int currentPos = stringBuffer.Length - 1;
				while ((currentPos > dotPosition) && (stringBuffer[currentPos] == '0'))
				{
					stringBuffer[currentPos--] = ' ';
				}
				if (stringBuffer[currentPos] == '.')
				{
					stringBuffer[currentPos] = ' ';
				}
				
				return stringBuffer.ToString().Trim();
			}
			return new System.Text.StringBuilder("" + value_Renamed).ToString();
		}
		
		/// <summary> Rounds a double and converts it into a formatted decimal-justified String.
		/// Trailing 0's are replaced with spaces.
		/// 
		/// </summary>
		/// <param name="value">the double value
		/// </param>
		/// <param name="width">the width of the string
		/// </param>
		/// <param name="afterDecimalPoint">the number of digits after the decimal point
		/// </param>
		/// <returns> the double as a formatted string
		/// </returns>
		public static System.String doubleToString(double value_Renamed, int width, int afterDecimalPoint)
		{
			
			System.String tempString = doubleToString(value_Renamed, afterDecimalPoint);
			char[] result;
			int dotPosition;
			
			if ((afterDecimalPoint >= width) || (tempString.IndexOf('E') != - 1))
			{
				// Protects sci notation
				return tempString;
			}
			
			// Initialize result
			result = new char[width];
			for (int i = 0; i < result.Length; i++)
			{
				result[i] = ' ';
			}
			
			if (afterDecimalPoint > 0)
			{
				// Get position of decimal point and insert decimal point
				dotPosition = tempString.IndexOf('.');
				if (dotPosition == - 1)
				{
					dotPosition = tempString.Length;
				}
				else
				{
					result[width - afterDecimalPoint - 1] = '.';
				}
			}
			else
			{
				dotPosition = tempString.Length;
			}
			
			
			int offset = width - afterDecimalPoint - dotPosition;
			if (afterDecimalPoint > 0)
			{
				offset--;
			}
			
			// Not enough room to decimal align within the supplied width
			if (offset < 0)
			{
				return tempString;
			}
			
			// Copy characters before decimal point
			for (int i = 0; i < dotPosition; i++)
			{
				result[offset + i] = tempString[i];
			}
			
			// Copy characters after decimal point
			for (int i = dotPosition + 1; i < tempString.Length; i++)
			{
				result[offset + i] = tempString[i];
			}
			
			return new System.String(result);
		}
		
		/// <summary> Returns the basic class of an array class (handles multi-dimensional
		/// arrays).
		/// </summary>
		/// <param name="o">       the array to inspect
		/// </param>
		/// <returns>         the class of the innermost elements
		/// </returns>
		public static System.Type getArrayClass(System.Type c)
		{
			if (c.GetElementType().IsArray)
				return getArrayClass(c.GetElementType());
			else
				return c.GetElementType();
		}
		
		/// <summary> Returns the dimensions of the given array. Even though the
		/// parameter is of type "Object" one can hand over primitve arrays, e.g.
		/// int[3] or double[2][4].
		/// 
		/// </summary>
		/// <param name="array">      the array to determine the dimensions for
		/// </param>
		/// <returns>            the dimensions of the array
		/// </returns>
		public static int getArrayDimensions(System.Type array)
		{
			if (array.GetElementType().IsArray)
				return 1 + getArrayDimensions(array.GetElementType());
			else
				return 1;
		}
		
		/// <summary> Returns the dimensions of the given array. Even though the
		/// parameter is of type "Object" one can hand over primitve arrays, e.g.
		/// int[3] or double[2][4].
		/// 
		/// </summary>
		/// <param name="array">      the array to determine the dimensions for
		/// </param>
		/// <returns>            the dimensions of the array
		/// </returns>
		public static int getArrayDimensions(System.Object array)
		{
			return getArrayDimensions(array.GetType());
		}
		
		/// <summary> Returns the given Array in a string representation. Even though the
		/// parameter is of type "Object" one can hand over primitve arrays, e.g.
		/// int[3] or double[2][4].
		/// 
		/// </summary>
		/// <param name="array">      the array to return in a string representation
		/// </param>
		/// <returns>            the array as string
		/// </returns>
		public static System.String arrayToString(System.Object array)
		{
			System.String result;
			int dimensions;
			int i;
			
			result = "";
			dimensions = getArrayDimensions(array);
			
			if (dimensions == 0)
			{
				result = "null";
			}
			else if (dimensions == 1)
			{
				for (i = 0; i < ((System.Array) array).Length; i++)
				{
					if (i > 0)
						result += ",";
					if (((System.Array) array).GetValue(i) == null)
						result += "null";
					else
					{
						//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Object.toString' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
						result += ((System.Array) array).GetValue(i).ToString();
					}
				}
			}
			else
			{
				for (i = 0; i < ((System.Array) array).Length; i++)
				{
					if (i > 0)
						result += ",";
					result += ("[" + arrayToString(((System.Array) array).GetValue(i)) + "]");
				}
			}
			
			return result;
		}
		
		/// <summary> Tests if a is equal to b.
		/// 
		/// </summary>
		/// <param name="a">a double
		/// </param>
		/// <param name="b">a double
		/// </param>
		public static bool eq(double a, double b)
		{
			
			return (a - b < SMALL) && (b - a < SMALL);
		}
		
		/// <summary> Checks if the given array contains any non-empty options.
		/// 
		/// </summary>
		/// <param name="strings">an array of strings
		/// </param>
		/// <exception cref="Exception">if there are any non-empty options
		/// </exception>
		public static void  checkForRemainingOptions(System.String[] options)
		{
			
			int illegalOptionsFound = 0;
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			
			if (options == null)
			{
				return ;
			}
			for (int i = 0; i < options.Length; i++)
			{
				if (options[i].Length > 0)
				{
					illegalOptionsFound++;
					text.Append(options[i] + ' ');
				}
			}
			if (illegalOptionsFound > 0)
			{
				throw new System.Exception("Illegal options: " + text);
			}
		}
		
		/// <summary> Checks if the given array contains the flag "-Char". Stops
		/// searching at the first marker "--". If the flag is found,
		/// it is replaced with the empty string.
		/// 
		/// </summary>
		/// <param name="flag">the character indicating the flag.
		/// </param>
		/// <param name="strings">the array of strings containing all the options.
		/// </param>
		/// <returns> true if the flag was found
		/// </returns>
		/// <exception cref="Exception">if an illegal option was found
		/// </exception>
		public static bool getFlag(char flag, System.String[] options)
		{
			return getFlag("" + flag, options);
		}
		
		/// <summary> Checks if the given array contains the flag "-String". Stops
		/// searching at the first marker "--". If the flag is found,
		/// it is replaced with the empty string.
		/// 
		/// </summary>
		/// <param name="flag">the String indicating the flag.
		/// </param>
		/// <param name="strings">the array of strings containing all the options.
		/// </param>
		/// <returns> true if the flag was found
		/// </returns>
		/// <exception cref="Exception">if an illegal option was found
		/// </exception>
		public static bool getFlag(System.String flag, System.String[] options)
		{
			
			if (options == null)
			{
				return false;
			}
			for (int i = 0; i < options.Length; i++)
			{
				if ((options[i].Length > 1) && (options[i][0] == '-'))
				{
					try
					{
						System.Double dummy = System.Double.Parse(options[i]);
					}
					catch (System.FormatException)
					{
						if (options[i].Equals("-" + flag))
						{
							options[i] = "";
							return true;
						}
						if (options[i][1] == '-')
						{
							return false;
						}
					}
				}
			}
			return false;
		}
		
		/// <summary> Gets an option indicated by a flag "-Char" from the given array
		/// of strings. Stops searching at the first marker "--". Replaces 
		/// flag and option with empty strings.
		/// 
		/// </summary>
		/// <param name="flag">the character indicating the option.
		/// </param>
		/// <param name="options">the array of strings containing all the options.
		/// </param>
		/// <returns> the indicated option or an empty string
		/// </returns>
		/// <exception cref="Exception">if the option indicated by the flag can't be found
		/// </exception>
		public static System.String getOption(char flag, System.String[] options)
		{
			return getOption("" + flag, options);
		}
		
		/// <summary> Gets an option indicated by a flag "-String" from the given array
		/// of strings. Stops searching at the first marker "--". Replaces 
		/// flag and option with empty strings.
		/// 
		/// </summary>
		/// <param name="flag">the String indicating the option.
		/// </param>
		/// <param name="options">the array of strings containing all the options.
		/// </param>
		/// <returns> the indicated option or an empty string
		/// </returns>
		/// <exception cref="Exception">if the option indicated by the flag can't be found
		/// </exception>
		public static System.String getOption(System.String flag, System.String[] options)
		{
			
			System.String newString;
			
			if (options == null)
				return "";
			for (int i = 0; i < options.Length; i++)
			{
				if ((options[i].Length > 0) && (options[i][0] == '-'))
				{
					
					// Check if it is a negative number
					try
					{
						System.Double dummy = System.Double.Parse(options[i]);
					}
					catch (System.FormatException e)
					{
						if (options[i].Equals("-" + flag))
						{
							if (i + 1 == options.Length)
							{
								throw new System.Exception("No value given for -" + flag + " option."+" "+e.ToString());
							}
							options[i] = "";
							newString = new System.Text.StringBuilder(options[i + 1]).ToString();
							options[i + 1] = "";
							return newString;
						}
						if (options[i][1] == '-')
						{
							return "";
						}
					}
				}
			}
			return "";
		}
		
		/// <summary> Quotes a string if it contains special characters.
		/// 
		/// The following rules are applied:
		/// 
		/// A character is backquoted version of it is one 
		/// of <tt>" ' % \ \n \r \t</tt>.
		/// 
		/// A string is enclosed within single quotes if a character has been
		/// backquoted using the previous rule above or contains 
		/// <tt>{ }</tt> or is exactly equal to the strings 
		/// <tt>, ? space or ""</tt> (empty string).
		/// 
		/// A quoted question mark distinguishes it from the missing value which
		/// is represented as an unquoted question mark in arff files.
		/// 
		/// </summary>
		/// <param name="string">the string to be quoted
		/// </param>
		/// <returns> the string (possibly quoted)
		/// </returns>
		public static System.String quote(System.String string_Renamed)
		{
			bool quote = false;
			
			// backquote the following characters 
			if ((string_Renamed.IndexOf('\n') != - 1) || (string_Renamed.IndexOf('\r') != - 1) || (string_Renamed.IndexOf('\'') != - 1) || (string_Renamed.IndexOf('"') != - 1) || (string_Renamed.IndexOf('\\') != - 1) || (string_Renamed.IndexOf('\t') != - 1) || (string_Renamed.IndexOf('%') != - 1))
			{
				string_Renamed = backQuoteChars(string_Renamed);
				quote = true;
			}
			
			// Enclose the string in 's if the string contains a recently added
			// backquote or contains one of the following characters.
			if ((quote == true) || (string_Renamed.IndexOf('{') != - 1) || (string_Renamed.IndexOf('}') != - 1) || (string_Renamed.IndexOf(',') != - 1) || (string_Renamed.Equals("?")) || (string_Renamed.IndexOf(' ') != - 1) || (string_Renamed.Equals("")))
			{
				string_Renamed = System.String.Concat((System.String.Concat("'", string_Renamed)), "'");
			}
			
			return string_Renamed;
		}
		
		/// <summary> Converts carriage returns and new lines in a string into \r and \n.
		/// Backquotes the following characters: ` " \ \t and %
		/// </summary>
		/// <param name="string">the string
		/// </param>
		/// <returns> the converted string
		/// </returns>
		public static System.String backQuoteChars(System.String string_Renamed)
		{
			
			int index;
			System.Text.StringBuilder newStringBuffer;
			
			// replace each of the following characters with the backquoted version
			char[] charsFind = new char[]{'\\', '\'', '\t', '"', '%'};
			System.String[] charsReplace = new System.String[]{"\\\\", "\\'", "\\t", "\\\"", "\\%"};
			for (int i = 0; i < charsFind.Length; i++)
			{
				if (string_Renamed.IndexOf((System.Char) charsFind[i]) != - 1)
				{
					newStringBuffer = new System.Text.StringBuilder();
					while ((index = string_Renamed.IndexOf((System.Char) charsFind[i])) != - 1)
					{
						if (index > 0)
						{
							newStringBuffer.Append(string_Renamed.Substring(0, (index) - (0)));
						}
						newStringBuffer.Append(charsReplace[i]);
						if ((index + 1) < string_Renamed.Length)
						{
							string_Renamed = string_Renamed.Substring(index + 1);
						}
						else
						{
							string_Renamed = "";
						}
					}
					newStringBuffer.Append(string_Renamed);
					string_Renamed = newStringBuffer.ToString();
				}
			}
			
			return Utils.convertNewLines(string_Renamed);
		}
		
		/// <summary> Converts carriage returns and new lines in a string into \r and \n.</summary>
		/// <param name="string">the string
		/// </param>
		/// <returns> the converted string
		/// </returns>
		public static System.String convertNewLines(System.String string_Renamed)
		{
			
			int index;
			
			// Replace with \n
			System.Text.StringBuilder newStringBuffer = new System.Text.StringBuilder();
			while ((index = string_Renamed.IndexOf('\n')) != - 1)
			{
				if (index > 0)
				{
					newStringBuffer.Append(string_Renamed.Substring(0, (index) - (0)));
				}
				newStringBuffer.Append('\\');
				newStringBuffer.Append('n');
				if ((index + 1) < string_Renamed.Length)
				{
					string_Renamed = string_Renamed.Substring(index + 1);
				}
				else
				{
					string_Renamed = "";
				}
			}
			newStringBuffer.Append(string_Renamed);
			string_Renamed = newStringBuffer.ToString();
			
			// Replace with \r
			newStringBuffer = new System.Text.StringBuilder();
			while ((index = string_Renamed.IndexOf('\r')) != - 1)
			{
				if (index > 0)
				{
					newStringBuffer.Append(string_Renamed.Substring(0, (index) - (0)));
				}
				newStringBuffer.Append('\\');
				newStringBuffer.Append('r');
				if ((index + 1) < string_Renamed.Length)
				{
					string_Renamed = string_Renamed.Substring(index + 1);
				}
				else
				{
					string_Renamed = "";
				}
			}
			newStringBuffer.Append(string_Renamed);
			return newStringBuffer.ToString();
		}
		
		
		/// <summary> Returns the secondary set of options (if any) contained in
		/// the supplied options array. The secondary set is defined to
		/// be any options after the first "--". These options are removed from
		/// the original options array.
		/// 
		/// </summary>
		/// <param name="options">the input array of options
		/// </param>
		/// <returns> the array of secondary options
		/// </returns>
		public static System.String[] partitionOptions(System.String[] options)
		{
			
			for (int i = 0; i < options.Length; i++)
			{
				if (options[i].Equals("--"))
				{
					options[i++] = "";
					System.String[] result = new System.String[options.Length - i];
					for (int j = i; j < options.Length; j++)
					{
						result[j - i] = options[j];
						options[j] = "";
					}
					return result;
				}
			}
			return new System.String[0];
		}
		
		/// <summary> The inverse operation of backQuoteChars().
		/// Converts back-quoted carriage returns and new lines in a string 
		/// to the corresponding character ('\r' and '\n').
		/// Also "un"-back-quotes the following characters: ` " \ \t and %
		/// </summary>
		/// <param name="string">the string
		/// </param>
		/// <returns> the converted string
		/// </returns>
		public static System.String unbackQuoteChars(System.String string_Renamed)
		{
			
			int index;
			System.Text.StringBuilder newStringBuffer;
			
			// replace each of the following characters with the backquoted version
			System.String[] charsFind = new System.String[]{"\\\\", "\\'", "\\t", "\\\"", "\\%"};
			char[] charsReplace = new char[]{'\\', '\'', '\t', '"', '%'};
			
			for (int i = 0; i < charsFind.Length; i++)
			{
				if (string_Renamed.IndexOf(charsFind[i]) != - 1)
				{
					newStringBuffer = new System.Text.StringBuilder();
					while ((index = string_Renamed.IndexOf(charsFind[i])) != - 1)
					{
						if (index > 0)
						{
							newStringBuffer.Append(string_Renamed.Substring(0, (index) - (0)));
						}
						newStringBuffer.Append(charsReplace[i]);
						if ((index + charsFind[i].Length) < string_Renamed.Length)
						{
							string_Renamed = string_Renamed.Substring(index + charsFind[i].Length);
						}
						else
						{
							string_Renamed = "";
						}
					}
					newStringBuffer.Append(string_Renamed);
					string_Renamed = newStringBuffer.ToString();
				}
			}
			return Utils.convertNewLines(string_Renamed);
		}
		
		/// <summary> Split up a string containing options into an array of strings,
		/// one for each option.
		/// 
		/// </summary>
		/// <param name="optionString">the string containing the options
		/// </param>
		/// <returns> the array of options
		/// </returns>
		public static System.String[] splitOptions(System.String quotedOptionString)
		{
			
			FastVector optionsVec = new FastVector();
			System.String str = new System.Text.StringBuilder(quotedOptionString).ToString();
			int i;
			
			while (true)
			{
				
				//trimLeft 
				i = 0;
				while ((i < str.Length) && (System.Char.IsWhiteSpace(str[i])))
					i++;
				str = str.Substring(i);
				
				//stop when str is empty
				if (str.Length == 0)
					break;
				
				//if str start with a double quote
				if (str[0] == '"')
				{
					
					//find the first not anti-slached double quote
					i = 1;
					while (i < str.Length)
					{
						if (str[i] == str[0])
							break;
						if (str[i] == '\\')
						{
							i += 1;
							if (i >= str.Length)
								throw new System.Exception("String should not finish with \\");
							if (str[i] != '\\' && str[i] != '"')
								throw new System.Exception("Unknow character \\" + str[i]);
						}
						i += 1;
					}
					if (i >= str.Length)
						throw new System.Exception("Quote parse error.");
					
					//add the founded string to the option vector (without quotes)
					System.String optStr = str.Substring(1, (i) - (1));
					optStr = unbackQuoteChars(optStr);
					optionsVec.addElement(optStr);
					str = str.Substring(i + 1);
				}
				else
				{
					//find first whiteSpace
					i = 0;
					while ((i < str.Length) && (!System.Char.IsWhiteSpace(str[i])))
						i++;
					
					//add the founded string to the option vector
					System.String optStr = str.Substring(0, (i) - (0));
					optionsVec.addElement(optStr);
					str = str.Substring(i);
				}
			}
			
			//convert optionsVec to an array of String
			System.String[] options = new System.String[optionsVec.size()];
			for (i = 0; i < optionsVec.size(); i++)
			{
				options[i] = ((System.String) optionsVec.elementAt(i));
			}
			return options;
		}
		
		/// <summary> Joins all the options in an option array into a single string,
		/// as might be used on the command line.
		/// 
		/// </summary>
		/// <param name="optionArray">the array of options
		/// </param>
		/// <returns> the string containing all options.
		/// </returns>
		public static System.String joinOptions(System.String[] optionArray)
		{
			
			System.String optionString = "";
			for (int i = 0; i < optionArray.Length; i++)
			{
				if (optionArray[i].Equals(""))
				{
					continue;
				}
				if (optionArray[i].IndexOf(' ') != - 1)
				{
					optionString += ('"' + optionArray[i] + '"');
				}
				else
				{
					optionString += optionArray[i];
				}
				optionString += " ";
			}
			return optionString.Trim();
		}
		
		/// <summary> Creates a new instance of an object given it's class name and
		/// (optional) arguments to pass to it's setOptions method. If the
		/// object implements OptionHandler and the options parameter is
		/// non-null, the object will have it's options set. Example use:<p>
		/// 
		/// <code> <pre>
		/// String classifierName = Utils.getOption('W', options);
		/// Classifier c = (Classifier)Utils.forName(Classifier.class,
		/// classifierName,
		/// options);
		/// setClassifier(c);
		/// </pre></code>
		/// 
		/// </summary>
		/// <param name="classType">the class that the instantiated object should
		/// be assignable to -- an exception is thrown if this is not the case
		/// </param>
		/// <param name="className">the fully qualified class name of the object
		/// </param>
		/// <param name="options">an array of options suitable for passing to setOptions. May
		/// be null. Any options accepted by the object will be removed from the
		/// array.
		/// </param>
		/// <returns> the newly created object, ready for use.
		/// </returns>
		/// <exception cref="Exception">if the class name is invalid, or if the
		/// class is not assignable to the desired class type, or the options
		/// supplied are not acceptable to the object
		/// </exception>
		public static System.Object forName(System.Type classType, System.String className, System.String[] options)
		{
			
			System.Type c = null;
			try
			{
				//UPGRADE_TODO: The differences in the format  of parameters for method 'java.lang.Class.forName'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
				c = System.Type.GetType(className);
			}
			catch (System.Exception ex)
			{
				throw new System.Exception("Can't find class called: " + className+" "+ex.ToString());
			}
			if (!classType.IsAssignableFrom(c))
			{
				//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Class.getName' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
				throw new System.Exception(classType.FullName + " is not assignable from " + className);
			}
			//UPGRADE_TODO: Method 'java.lang.Class.newInstance' was converted to 'System.Activator.CreateInstance' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javalangClassnewInstance'"
			System.Object o = System.Activator.CreateInstance(c);
			//		if ((o instanceof OptionHandler)
			//			&& (options != null)) 
			//		{
			//			((OptionHandler)o).setOptions(options);
			//			Utils.checkForRemainingOptions(options);
			//		}
			return o;
		}
		
		/// <summary> Computes entropy for an array of integers.
		/// 
		/// </summary>
		/// <param name="counts">array of counts
		/// </param>
		/// <returns> - a log2 a - b log2 b - c log2 c + (a+b+c) log2 (a+b+c)
		/// when given array [a b c]
		/// </returns>
		public static double info(int[] counts)
		{
			
			int total = 0;
			double x = 0;
			for (int j = 0; j < counts.Length; j++)
			{
				x -= xlogx(counts[j]);
				total += counts[j];
			}
			return x + xlogx(total);
		}
		
		/// <summary> Tests if a is smaller or equal to b.
		/// 
		/// </summary>
		/// <param name="a">a double
		/// </param>
		/// <param name="b">a double
		/// </param>
		public static bool smOrEq(double a, double b)
		{
			
			return (a - b < SMALL);
		}
		
		/// <summary> Tests if a is greater or equal to b.
		/// 
		/// </summary>
		/// <param name="a">a double
		/// </param>
		/// <param name="b">a double
		/// </param>
		public static bool grOrEq(double a, double b)
		{
			
			return (b - a < SMALL);
		}
		
		/// <summary> Tests if a is smaller than b.
		/// 
		/// </summary>
		/// <param name="a">a double
		/// </param>
		/// <param name="b">a double
		/// </param>
		public static bool sm(double a, double b)
		{
			
			return (b - a > SMALL);
		}
		
		/// <summary> Tests if a is greater than b.
		/// 
		/// </summary>
		/// <param name="a">a double
		/// </param>
		/// <param name="b">a double 
		/// </param>
		public static bool gr(double a, double b)
		{
			
			return (a - b > SMALL);
		}
		
		/// <summary> Returns the kth-smallest value in the array.
		/// 
		/// </summary>
		/// <param name="array">the array of integers
		/// </param>
		/// <param name="k">the value of k
		/// </param>
		/// <returns> the kth-smallest value
		/// </returns>
		public static double kthSmallestValue(int[] array, int k)
		{
			
			int[] index = new int[array.Length];
			
			for (int i = 0; i < index.Length; i++)
			{
				index[i] = i;
			}
			
			return array[index[select(array, index, 0, array.Length - 1, k)]];
		}
		
		/// <summary> Returns the kth-smallest value in the array
		/// 
		/// </summary>
		/// <param name="array">the array of double
		/// </param>
		/// <param name="k">the value of k
		/// </param>
		/// <returns> the kth-smallest value
		/// </returns>
		public static double kthSmallestValue(double[] array, int k)
		{
			
			int[] index = new int[array.Length];
			
			for (int i = 0; i < index.Length; i++)
			{
				index[i] = i;
			}
			
			return array[index[select(array, index, 0, array.Length - 1, k)]];
		}
		
		/// <summary> Returns the logarithm of a for base 2.
		/// 
		/// </summary>
		/// <param name="a">a double
		/// </param>
		public static double log2(double a)
		{
			
			return System.Math.Log(a) / log2_Renamed_Field;
		}
		
		/// <summary> Returns index of maximum element in a given
		/// array of doubles. First maximum is returned.
		/// 
		/// </summary>
		/// <param name="doubles">the array of doubles
		/// </param>
		/// <returns> the index of the maximum element
		/// </returns>
		public static int maxIndex(double[] doubles)
		{
			
			double maximum = 0;
			int maxIndex = 0;
			
			for (int i = 0; i < doubles.Length; i++)
			{
				if ((i == 0) || (doubles[i] > maximum))
				{
					maxIndex = i;
					maximum = doubles[i];
				}
			}
			
			return maxIndex;
		}
		
		/// <summary> Returns index of maximum element in a given
		/// array of integers. First maximum is returned.
		/// 
		/// </summary>
		/// <param name="ints">the array of integers
		/// </param>
		/// <returns> the index of the maximum element
		/// </returns>
		public static int maxIndex(int[] ints)
		{
			
			int maximum = 0;
			int maxIndex = 0;
			
			for (int i = 0; i < ints.Length; i++)
			{
				if ((i == 0) || (ints[i] > maximum))
				{
					maxIndex = i;
					maximum = ints[i];
				}
			}
			
			return maxIndex;
		}
		
		/// <summary> Computes the mean for an array of doubles.
		/// 
		/// </summary>
		/// <param name="vector">the array
		/// </param>
		/// <returns> the mean
		/// </returns>
		public static double mean(double[] vector)
		{
			
			double sum = 0;
			
			if (vector.Length == 0)
			{
				return 0;
			}
			for (int i = 0; i < vector.Length; i++)
			{
				sum += vector[i];
			}
			return sum / (double) vector.Length;
		}
		
		/// <summary> Returns index of minimum element in a given
		/// array of integers. First minimum is returned.
		/// 
		/// </summary>
		/// <param name="ints">the array of integers
		/// </param>
		/// <returns> the index of the minimum element
		/// </returns>
		public static int minIndex(int[] ints)
		{
			
			int minimum = 0;
			int minIndex = 0;
			
			for (int i = 0; i < ints.Length; i++)
			{
				if ((i == 0) || (ints[i] < minimum))
				{
					minIndex = i;
					minimum = ints[i];
				}
			}
			
			return minIndex;
		}
		
		/// <summary> Returns index of minimum element in a given
		/// array of doubles. First minimum is returned.
		/// 
		/// </summary>
		/// <param name="doubles">the array of doubles
		/// </param>
		/// <returns> the index of the minimum element
		/// </returns>
		public static int minIndex(double[] doubles)
		{
			
			double minimum = 0;
			int minIndex = 0;
			
			for (int i = 0; i < doubles.Length; i++)
			{
				if ((i == 0) || (doubles[i] < minimum))
				{
					minIndex = i;
					minimum = doubles[i];
				}
			}
			
			return minIndex;
		}
		
		/// <summary> Normalizes the doubles in the array by their sum.
		/// 
		/// </summary>
		/// <param name="doubles">the array of double
		/// </param>
		/// <exception cref="IllegalArgumentException">if sum is Zero or NaN
		/// </exception>
		public static void  normalize(double[] doubles)
		{
			
			double sum = 0;
			for (int i = 0; i < doubles.Length; i++)
			{
				sum += doubles[i];
			}
			normalize(doubles, sum);
		}
		
		/// <summary> Normalizes the doubles in the array using the given value.
		/// 
		/// </summary>
		/// <param name="doubles">the array of double
		/// </param>
		/// <param name="sum">the value by which the doubles are to be normalized
		/// </param>
		/// <exception cref="IllegalArgumentException">if sum is zero or NaN
		/// </exception>
		public static void  normalize(double[] doubles, double sum)
		{
			
			if (System.Double.IsNaN(sum))
			{
				throw new System.ArgumentException("Can't normalize array. Sum is NaN.");
			}
			if (sum == 0)
			{
				// Maybe this should just be a return.
				throw new System.ArgumentException("Can't normalize array. Sum is zero.");
			}
			for (int i = 0; i < doubles.Length; i++)
			{
				doubles[i] /= sum;
			}
		}
		
		/// <summary> Converts an array containing the natural logarithms of
		/// probabilities stored in a vector back into probabilities.
		/// The probabilities are assumed to sum to one.
		/// 
		/// </summary>
		/// <param name="a">an array holding the natural logarithms of the probabilities
		/// </param>
		/// <returns> the converted array 
		/// </returns>
		public static double[] logs2probs(double[] a)
		{
			
			double max = a[maxIndex(a)];
			double sum = 0.0;
			
			double[] result = new double[a.Length];
			for (int i = 0; i < a.Length; i++)
			{
				result[i] = System.Math.Exp(a[i] - max);
				sum += result[i];
			}
			
			normalize(result, sum);
			
			return result;
		}
		
		/// <summary> Rounds a double to the next nearest integer value. The JDK version
		/// of it doesn't work properly.
		/// 
		/// </summary>
		/// <param name="value">the double value
		/// </param>
		/// <returns> the resulting integer value
		/// </returns>
		public static int round(double value_Renamed)
		{
			
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			int roundedValue = value_Renamed > 0?(int) (value_Renamed + 0.5):- (int) (System.Math.Abs(value_Renamed) + 0.5);
			
			return roundedValue;
		}
		
		/// <summary> Rounds a double to the next nearest integer value in a probabilistic
		/// fashion (e.g. 0.8 has a 20% chance of being rounded down to 0 and a
		/// 80% chance of being rounded up to 1). In the limit, the average of
		/// the rounded numbers generated by this procedure should converge to
		/// the original double.
		/// 
		/// </summary>
		/// <param name="value">the double value
		/// </param>
		/// <returns> the resulting integer value
		/// </returns>
		public static int probRound(double value_Renamed, System.Random rand)
		{
			
			if (value_Renamed >= 0)
			{
				double lower = System.Math.Floor(value_Renamed);
				double prob = value_Renamed - lower;
				if (rand.NextDouble() < prob)
				{
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					return (int) lower + 1;
				}
				else
				{
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					return (int) lower;
				}
			}
			else
			{
				double lower = System.Math.Floor(System.Math.Abs(value_Renamed));
				double prob = System.Math.Abs(value_Renamed) - lower;
				if (rand.NextDouble() < prob)
				{
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					return - ((int) lower + 1);
				}
				else
				{
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					return - (int) lower;
				}
			}
		}
		
		/// <summary> Rounds a double to the given number of decimal places.
		/// 
		/// </summary>
		/// <param name="value">the double value
		/// </param>
		/// <param name="afterDecimalPoint">the number of digits after the decimal point
		/// </param>
		/// <returns> the double rounded to the given precision
		/// </returns>
		public static double roundDouble(double value_Renamed, int afterDecimalPoint)
		{
			
			double mask = System.Math.Pow(10.0, (double) afterDecimalPoint);
			
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			//UPGRADE_TODO: Method 'java.lang.Math.round' was converted to 'System.Math.Round' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javalangMathround_double'"
			return (double) ((long) System.Math.Round(value_Renamed * mask)) / mask;
		}
		
		/// <summary> Sorts a given array of integers in ascending order and returns an 
		/// array of integers with the positions of the elements of the original 
		/// array in the sorted array. The sort is stable. (Equal elements remain
		/// in their original order.)
		/// 
		/// </summary>
		/// <param name="array">this array is not changed by the method!
		/// </param>
		/// <returns> an array of integers with the positions in the sorted
		/// array.
		/// </returns>
		public static int[] sort(int[] array)
		{
			
			int[] index = new int[array.Length];
			int[] newIndex = new int[array.Length];
			int[] helpIndex;
			int numEqual;
			
			for (int i = 0; i < index.Length; i++)
			{
				index[i] = i;
			}
			quickSort(array, index, 0, array.Length - 1);
			
			// Make sort stable
			int i2 = 0;
			while (i2 < index.Length)
			{
				numEqual = 1;
				for (int j = i2 + 1; ((j < index.Length) && (array[index[i2]] == array[index[j]])); j++)
				{
					numEqual++;
				}
				if (numEqual > 1)
				{
					helpIndex = new int[numEqual];
					for (int j = 0; j < numEqual; j++)
					{
						helpIndex[j] = i2 + j;
					}
					quickSort(index, helpIndex, 0, numEqual - 1);
					for (int j = 0; j < numEqual; j++)
					{
						newIndex[i2 + j] = index[helpIndex[j]];
					}
					i2 += numEqual;
				}
				else
				{
					newIndex[i2] = index[i2];
					i2++;
				}
			}
			return newIndex;
		}
		
		/// <summary> Sorts a given array of doubles in ascending order and returns an
		/// array of integers with the positions of the elements of the
		/// original array in the sorted array. NOTE THESE CHANGES: the sort
		/// is no longer stable and it doesn't use safe floating-point
		/// comparisons anymore. Occurrences of Double.NaN are treated as 
		/// Double.MAX_VALUE
		/// 
		/// </summary>
		/// <param name="array">this array is not changed by the method!
		/// </param>
		/// <returns> an array of integers with the positions in the sorted
		/// array.  
		/// </returns>
		public static int[] sort(double[] array)
		{
			
			int[] index = new int[array.Length];
			array = new double[array.Length];
			array.CopyTo(array, 0);
			for (int i = 0; i < index.Length; i++)
			{
				index[i] = i;
				if (System.Double.IsNaN(array[i]))
				{
					//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
					array[i] = System.Double.MaxValue;
				}
			}
			quickSort(array, index, 0, array.Length - 1);
			return index;
		}
		
		/// <summary> Sorts a given array of doubles in ascending order and returns an 
		/// array of integers with the positions of the elements of the original 
		/// array in the sorted array. The sort is stable (Equal elements remain
		/// in their original order.) Occurrences of Double.NaN are treated as 
		/// Double.MAX_VALUE
		/// 
		/// </summary>
		/// <param name="array">this array is not changed by the method!
		/// </param>
		/// <returns> an array of integers with the positions in the sorted
		/// array.
		/// </returns>
		public static int[] stableSort(double[] array)
		{
			
			int[] index = new int[array.Length];
			int[] newIndex = new int[array.Length];
			int[] helpIndex;
			int numEqual;
			
			array = new double[array.Length];
			array.CopyTo(array, 0);
			for (int i = 0; i < index.Length; i++)
			{
				index[i] = i;
				if (System.Double.IsNaN(array[i]))
				{
					//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
					array[i] = System.Double.MaxValue;
				}
			}
			quickSort(array, index, 0, array.Length - 1);
			
			// Make sort stable
			
			int i2 = 0;
			while (i2 < index.Length)
			{
				numEqual = 1;
				for (int j = i2 + 1; ((j < index.Length) && Utils.eq(array[index[i2]], array[index[j]])); j++)
					numEqual++;
				if (numEqual > 1)
				{
					helpIndex = new int[numEqual];
					for (int j = 0; j < numEqual; j++)
						helpIndex[j] = i2 + j;
					quickSort(index, helpIndex, 0, numEqual - 1);
					for (int j = 0; j < numEqual; j++)
						newIndex[i2 + j] = index[helpIndex[j]];
					i2 += numEqual;
				}
				else
				{
					newIndex[i2] = index[i2];
					i2++;
				}
			}
			
			return newIndex;
		}
		
		/// <summary> Computes the variance for an array of doubles.
		/// 
		/// </summary>
		/// <param name="vector">the array
		/// </param>
		/// <returns> the variance
		/// </returns>
		public static double variance(double[] vector)
		{
			
			double sum = 0, sumSquared = 0;
			
			if (vector.Length <= 1)
			{
				return 0;
			}
			for (int i = 0; i < vector.Length; i++)
			{
				sum += vector[i];
				sumSquared += (vector[i] * vector[i]);
			}
			double result = (sumSquared - (sum * sum / (double) vector.Length)) / (double) (vector.Length - 1);
			
			// We don't like negative variance
			if (result < 0)
			{
				return 0;
			}
			else
			{
				return result;
			}
		}
		
		/// <summary> Computes the sum of the elements of an array of doubles.
		/// 
		/// </summary>
		/// <param name="doubles">the array of double
		/// </param>
		/// <returns> the sum of the elements
		/// </returns>
		public static double sum(double[] doubles)
		{
			
			double sum = 0;
			
			for (int i = 0; i < doubles.Length; i++)
			{
				sum += doubles[i];
			}
			return sum;
		}
		
		/// <summary> Computes the sum of the elements of an array of integers.
		/// 
		/// </summary>
		/// <param name="ints">the array of integers
		/// </param>
		/// <returns> the sum of the elements
		/// </returns>
		public static int sum(int[] ints)
		{
			
			int sum = 0;
			
			for (int i = 0; i < ints.Length; i++)
			{
				sum += ints[i];
			}
			return sum;
		}
		
		/// <summary> Returns c*log2(c) for a given integer value c.
		/// 
		/// </summary>
		/// <param name="c">an integer value
		/// </param>
		/// <returns> c*log2(c) (but is careful to return 0 if c is 0)
		/// </returns>
		public static double xlogx(int c)
		{
			
			if (c == 0)
			{
				return 0.0;
			}
			return c * Utils.log2((double) c);
		}
		
		/// <summary> Partitions the instances around a pivot. Used by quicksort and
		/// kthSmallestValue.
		/// 
		/// </summary>
		/// <param name="array">the array of doubles to be sorted
		/// </param>
		/// <param name="index">the index into the array of doubles
		/// </param>
		/// <param name="left">the first index of the subset 
		/// </param>
		/// <param name="right">the last index of the subset 
		/// 
		/// </param>
		/// <returns> the index of the middle element
		/// </returns>
		private static int partition(double[] array, int[] index, int l, int r)
		{
			
			double pivot = array[index[(l + r) / 2]];
			int help;
			
			while (l < r)
			{
				while ((array[index[l]] < pivot) && (l < r))
				{
					l++;
				}
				while ((array[index[r]] > pivot) && (l < r))
				{
					r--;
				}
				if (l < r)
				{
					help = index[l];
					index[l] = index[r];
					index[r] = help;
					l++;
					r--;
				}
			}
			if ((l == r) && (array[index[r]] > pivot))
			{
				r--;
			}
			
			return r;
		}
		
		/// <summary> Partitions the instances around a pivot. Used by quicksort and
		/// kthSmallestValue.
		/// 
		/// </summary>
		/// <param name="array">the array of integers to be sorted
		/// </param>
		/// <param name="index">the index into the array of integers
		/// </param>
		/// <param name="left">the first index of the subset 
		/// </param>
		/// <param name="right">the last index of the subset 
		/// 
		/// </param>
		/// <returns> the index of the middle element
		/// </returns>
		private static int partition(int[] array, int[] index, int l, int r)
		{
			
			double pivot = array[index[(l + r) / 2]];
			int help;
			
			while (l < r)
			{
				while ((array[index[l]] < pivot) && (l < r))
				{
					l++;
				}
				while ((array[index[r]] > pivot) && (l < r))
				{
					r--;
				}
				if (l < r)
				{
					help = index[l];
					index[l] = index[r];
					index[r] = help;
					l++;
					r--;
				}
			}
			if ((l == r) && (array[index[r]] > pivot))
			{
				r--;
			}
			
			return r;
		}
		
		/// <summary> Implements quicksort according to Manber's "Introduction to
		/// Algorithms".
		/// 
		/// </summary>
		/// <param name="array">the array of doubles to be sorted
		/// </param>
		/// <param name="index">the index into the array of doubles
		/// </param>
		/// <param name="left">the first index of the subset to be sorted
		/// </param>
		/// <param name="right">the last index of the subset to be sorted
		/// </param>
		//@ requires 0 <= first && first <= right && right < array.length;
		//@ requires (\forall int i; 0 <= i && i < index.length; 0 <= index[i] && index[i] < array.length);
		//@ requires array != index;
		//  assignable index;
		private static void  quickSort(double[] array, int[] index, int left, int right)
		{
			
			if (left < right)
			{
				int middle = partition(array, index, left, right);
				quickSort(array, index, left, middle);
				quickSort(array, index, middle + 1, right);
			}
		}
		
		/// <summary> Implements quicksort according to Manber's "Introduction to
		/// Algorithms".
		/// 
		/// </summary>
		/// <param name="array">the array of integers to be sorted
		/// </param>
		/// <param name="index">the index into the array of integers
		/// </param>
		/// <param name="left">the first index of the subset to be sorted
		/// </param>
		/// <param name="right">the last index of the subset to be sorted
		/// </param>
		//@ requires 0 <= first && first <= right && right < array.length;
		//@ requires (\forall int i; 0 <= i && i < index.length; 0 <= index[i] && index[i] < array.length);
		//@ requires array != index;
		//  assignable index;
		private static void  quickSort(int[] array, int[] index, int left, int right)
		{
			
			if (left < right)
			{
				int middle = partition(array, index, left, right);
				quickSort(array, index, left, middle);
				quickSort(array, index, middle + 1, right);
			}
		}
		
		/// <summary> Implements computation of the kth-smallest element according
		/// to Manber's "Introduction to Algorithms".
		/// 
		/// </summary>
		/// <param name="array">the array of double
		/// </param>
		/// <param name="index">the index into the array of doubles
		/// </param>
		/// <param name="left">the first index of the subset 
		/// </param>
		/// <param name="right">the last index of the subset 
		/// </param>
		/// <param name="k">the value of k
		/// 
		/// </param>
		/// <returns> the index of the kth-smallest element
		/// </returns>
		//@ requires 0 <= first && first <= right && right < array.length;
		private static int select(double[] array, int[] index, int left, int right, int k)
		{
			
			if (left == right)
			{
				return left;
			}
			else
			{
				int middle = partition(array, index, left, right);
				if ((middle - left + 1) >= k)
				{
					return select(array, index, left, middle, k);
				}
				else
				{
					return select(array, index, middle + 1, right, k - (middle - left + 1));
				}
			}
		}
		
		/// <summary> Implements computation of the kth-smallest element according
		/// to Manber's "Introduction to Algorithms".
		/// 
		/// </summary>
		/// <param name="array">the array of integers
		/// </param>
		/// <param name="index">the index into the array of integers
		/// </param>
		/// <param name="left">the first index of the subset 
		/// </param>
		/// <param name="right">the last index of the subset 
		/// </param>
		/// <param name="k">the value of k
		/// 
		/// </param>
		/// <returns> the index of the kth-smallest element
		/// </returns>
		//@ requires 0 <= first && first <= right && right < array.length;
		private static int select(int[] array, int[] index, int left, int right, int k)
		{
			
			if (left == right)
			{
				return left;
			}
			else
			{
				int middle = partition(array, index, left, right);
				if ((middle - left + 1) >= k)
				{
					return select(array, index, left, middle, k);
				}
				else
				{
					return select(array, index, middle + 1, right, k - (middle - left + 1));
				}
			}
		}
		
		/// <summary> Main method for testing this class.
		/// 
		/// </summary>
		/// <param name="ops">some dummy options
		/// </param>
		//	public static void main(String[] ops) 
		//	{
		//
		//		double[] doublesWithNaN = {4.5, 6.7, Double.NaN, 3.4, 4.8, 1.2, 3.4};
		//		double[] doubles = {4.5, 6.7, 6.7, 3.4, 4.8, 1.2, 3.4, 6.7, 6.7, 3.4};
		//		int[] ints = {12, 6, 2, 18, 16, 6, 7, 5, 18, 18, 17};
		//
		//		try 
		//		{
		//
		//			// Option handling
		//			System.out.println("First option split up:");
		//			if (ops.length > 0) 
		//			{
		//				String[] firstOptionSplitUp = Utils.splitOptions(ops[0]);
		//				for (int i = 0; i < firstOptionSplitUp.length; i ++) 
		//				{
		//					System.out.println(firstOptionSplitUp[i]);
		//				}
		//			}					       
		//			System.out.println("Partitioned options: ");
		//			String[] partitionedOptions = Utils.partitionOptions(ops);
		//			for (int i  = 0; i < partitionedOptions.length; i++) 
		//			{
		//				System.out.println(partitionedOptions[i]);
		//			}
		//			System.out.println("Get flag -f: " + Utils.getFlag('f', ops));
		//			System.out.println("Get option -o: " + Utils.getOption('o', ops));
		//			System.out.println("Checking for remaining options... ");
		//			Utils.checkForRemainingOptions(ops);
		//      
		//			// Statistics
		//			System.out.println("Original array with NaN (doubles): ");
		//			for (int i = 0; i < doublesWithNaN.length; i++) 
		//			{
		//				System.out.print(doublesWithNaN[i] + " ");
		//			}
		//			System.out.println();
		//			System.out.println("Original array (doubles): ");
		//			for (int i = 0; i < doubles.length; i++) 
		//			{
		//				System.out.print(doubles[i] + " ");
		//			}
		//			System.out.println();
		//			System.out.println("Original array (ints): ");
		//			for (int i = 0; i < ints.length; i++) 
		//			{
		//				System.out.print(ints[i] + " ");
		//			}
		//			System.out.println();
		//			System.out.println("Correlation: " + Utils.correlation(doubles, doubles, 
		//				doubles.length));
		//			System.out.println("Mean: " + Utils.mean(doubles));
		//			System.out.println("Variance: " + Utils.variance(doubles));
		//			System.out.println("Sum (doubles): " + Utils.sum(doubles));
		//			System.out.println("Sum (ints): " + Utils.sum(ints));
		//			System.out.println("Max index (doubles): " + Utils.maxIndex(doubles));
		//			System.out.println("Max index (ints): " + Utils.maxIndex(ints));
		//			System.out.println("Min index (doubles): " + Utils.minIndex(doubles));
		//			System.out.println("Min index (ints): " + Utils.minIndex(ints));
		//			System.out.println("Median (doubles): " + 
		//				Utils.kthSmallestValue(doubles, doubles.length / 2));
		//			System.out.println("Median (ints): " + 
		//				Utils.kthSmallestValue(ints, ints.length / 2));
		//
		//			// Sorting and normalizing
		//			System.out.println("Sorted array with NaN (doubles): ");
		//			int[] sorted = Utils.sort(doublesWithNaN);
		//			for (int i = 0; i < doublesWithNaN.length; i++) 
		//			{
		//				System.out.print(doublesWithNaN[sorted[i]] + " ");
		//			}
		//			System.out.println();
		//			System.out.println("Sorted array (doubles): ");
		//			sorted = Utils.sort(doubles);
		//			for (int i = 0; i < doubles.length; i++) 
		//			{
		//				System.out.print(doubles[sorted[i]] + " ");
		//			}
		//			System.out.println();
		//			System.out.println("Sorted array (ints): ");
		//			sorted = Utils.sort(ints);
		//			for (int i = 0; i < ints.length; i++) 
		//			{
		//				System.out.print(ints[sorted[i]] + " ");
		//			}
		//			System.out.println();
		//			System.out.println("Indices from stable sort (doubles): ");
		//			sorted = Utils.stableSort(doubles);
		//			for (int i = 0; i < doubles.length; i++) 
		//			{
		//				System.out.print(sorted[i] + " ");
		//			}
		//			System.out.println();
		//			System.out.println("Indices from sort (ints): ");
		//			sorted = Utils.sort(ints);
		//			for (int i = 0; i < ints.length; i++) 
		//			{
		//				System.out.print(sorted[i] + " ");
		//			}
		//			System.out.println();
		//			System.out.println("Normalized array (doubles): ");
		//			Utils.normalize(doubles);
		//			for (int i = 0; i < doubles.length; i++) 
		//			{
		//				System.out.print(doubles[i] + " ");
		//			}
		//			System.out.println();
		//			System.out.println("Normalized again (doubles): ");
		//			Utils.normalize(doubles, Utils.sum(doubles));
		//			for (int i = 0; i < doubles.length; i++) 
		//			{
		//				System.out.print(doubles[i] + " ");
		//			}
		//			System.out.println();
		//      
		//			// Pretty-printing
		//			System.out.println("-4.58: " + Utils.doubleToString(-4.57826535, 2));
		//			System.out.println("-6.78: " + Utils.doubleToString(-6.78214234, 6,2));
		//      
		//			// Comparisons
		//			System.out.println("5.70001 == 5.7 ? " + Utils.eq(5.70001, 5.7));
		//			System.out.println("5.70001 > 5.7 ? " + Utils.gr(5.70001, 5.7));
		//			System.out.println("5.70001 >= 5.7 ? " + Utils.grOrEq(5.70001, 5.7));
		//			System.out.println("5.7 < 5.70001 ? " + Utils.sm(5.7, 5.70001));
		//			System.out.println("5.7 <= 5.70001 ? " + Utils.smOrEq(5.7, 5.70001));
		//      
		//			// Math
		//			System.out.println("Info (ints): " + Utils.info(ints));
		//			System.out.println("log2(4.6): " + Utils.log2(4.6));
		//			System.out.println("5 * log(5): " + Utils.xlogx(5));
		//			System.out.println("5.5 rounded: " + Utils.round(5.5));
		//			System.out.println("5.55555 rounded to 2 decimal places: " + 
		//				Utils.roundDouble(5.55555, 2));
		//      
		//			// Arrays
		//			System.out.println("Array-Dimensions of 'new int[][]': " + Utils.getArrayDimensions(new int[][]{}));
		//			System.out.println("Array-Dimensions of 'new int[][]{{1,2,3},{4,5,6}}': " + Utils.getArrayDimensions(new int[][]{{1,2,3},{4,5,6}}));
		//			String[][][] s = new String[3][4][];
		//			System.out.println("Array-Dimensions of 'new String[3][4][]': " + Utils.getArrayDimensions(s));
		//		} 
		//		catch (Exception e) 
		//		{
		//			e.printStackTrace();
		//		}
		//	}
	}
}