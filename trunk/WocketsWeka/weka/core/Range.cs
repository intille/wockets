/*
*    Range.java
*    Copyright (C) 1999 Len Trigg
*
*/
using System;
namespace weka.core
{
	
	/// <summary> Class representing a range of cardinal numbers. The range is set by a 
	/// string representation such as: <P>
	/// 
	/// <code>
	/// all
	/// first-last
	/// 1,2,3,4
	/// </code> <P>
	/// or combinations thereof. The range is internally converted from
	/// 1-based to 0-based (so methods that set or get numbers not in string
	/// format should use 0-based numbers).
	/// 
	/// </summary>
	/// <author>  Len Trigg (trigg@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.14 $
	/// </version>
#if !PocketPC
    [Serializable]
#endif
	public class Range
	{
		/// <summary> Sets the value of "last".
		/// 
		/// </summary>
		/// <param name="newUpper">the value of "last"
		/// </param>
		virtual public int Upper
		{
			set
			{
				
				if (value >= 0)
				{
					m_Upper = value;
					setFlags();
				}
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets whether the range sense is inverted, i.e. all <i>except</i>
		/// the values included by the range string are selected.
		/// 
		/// </summary>
		/// <returns> whether the matching sense is inverted
		/// </returns>
		/// <summary> Sets whether the range sense is inverted, i.e. all <i>except</i>
		/// the values included by the range string are selected.
		/// 
		/// </summary>
		/// <param name="newSetting">true if the matching sense is inverted
		/// </param>
		virtual public bool Invert
		{
			//@ensures \result <==> m_Invert;
			
			get
			{
				
				return m_Invert;
			}
			
			set
			{
				
				m_Invert = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the string representing the selected range of values
		/// 
		/// </summary>
		/// <returns> the range selection string
		/// </returns>
		/// <summary> Sets the ranges from a string representation. Note that setUpper()
		/// must be called afterwards for ranges to be actually set internally.
		/// 
		/// </summary>
		/// <param name="rangeList">the comma separated list of ranges. The empty
		/// string sets the range to empty.
		/// </param>
		/// <exception cref="IllegalArgumentException">if the rangeList was not well formed
		/// </exception>
		virtual public System.String Ranges
		{
			
			
			get
			{
				
				System.String result = null;
				System.Collections.IEnumerator enu = m_RangeStrings.GetEnumerator();
				//UPGRADE_TODO: Method 'java.util.Enumeration.hasMoreElements' was converted to 'System.Collections.IEnumerator.MoveNext' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationhasMoreElements'"
				while (enu.MoveNext())
				{
					if (result == null)
					{
						//UPGRADE_TODO: Method 'java.util.Enumeration.nextElement' was converted to 'System.Collections.IEnumerator.Current' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationnextElement'"
						result = ((System.String) enu.Current);
					}
					else
					{
						//UPGRADE_TODO: Method 'java.util.Enumeration.nextElement' was converted to 'System.Collections.IEnumerator.Current' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationnextElement'"
						result += (',' + (System.String) enu.Current);
					}
				}
				return (result == null)?"":result;
			}
			
			//@requires rangeList != null;
			//@assignable m_RangeStrings,m_SelectFlags;
			
			set
			{
				
				System.Collections.ArrayList ranges = System.Collections.ArrayList.Synchronized(new System.Collections.ArrayList(10));
				
				// Split the rangeList up into the vector
				while (!value.Equals(""))
				{
					System.String range = value.Trim();
					int commaLoc = value.IndexOf(',');
					if (commaLoc != - 1)
					{
						range = value.Substring(0, (commaLoc) - (0)).Trim();
						value = value.Substring(commaLoc + 1).Trim();
					}
					else
					{
						value = "";
					}
					if (!range.Equals(""))
					{
						ranges.Add(range);
					}
				}
				m_RangeStrings = ranges;
				m_SelectFlags = null;
			}
			
		}
		/// <summary> Gets an array containing all the selected values, in the order
		/// that they were selected (or ascending order if range inversion is on)
		/// 
		/// </summary>
		/// <returns> the array of selected values
		/// </returns>
		/// <exception cref="RuntimeException">if the upper limit of the range hasn't been defined
		/// </exception>
		virtual public int[] Selection
		{
			//@requires m_Upper >= 0;
			
			get
			{
				
				if (m_Upper == - 1)
				{
					throw new System.SystemException("No upper limit has been specified for range");
				}
				int[] selectIndices = new int[m_Upper + 1];
				int numSelected = 0;
				if (m_Invert)
				{
					for (int i = 0; i <= m_Upper; i++)
					{
						if (!m_SelectFlags[i])
						{
							selectIndices[numSelected++] = i;
						}
					}
				}
				else
				{
					System.Collections.IEnumerator enu = m_RangeStrings.GetEnumerator();
					//UPGRADE_TODO: Method 'java.util.Enumeration.hasMoreElements' was converted to 'System.Collections.IEnumerator.MoveNext' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationhasMoreElements'"
					while (enu.MoveNext())
					{
						//UPGRADE_TODO: Method 'java.util.Enumeration.nextElement' was converted to 'System.Collections.IEnumerator.Current' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationnextElement'"
						System.String currentRange = (System.String) enu.Current;
						int start = rangeLower(currentRange);
						int end = rangeUpper(currentRange);
						for (int i = start; (i <= m_Upper) && (i <= end); i++)
						{
							if (m_SelectFlags[i])
							{
								selectIndices[numSelected++] = i;
							}
						}
					}
				}
				int[] result = new int[numSelected];
				Array.Copy(selectIndices, 0, result, 0, numSelected);
				return result;
			}
			
		}
		
		/*@non_null spec_public@*/ /// <summary>Record the string representations of the columns to delete </summary>
		internal System.Collections.ArrayList m_RangeStrings = System.Collections.ArrayList.Synchronized(new System.Collections.ArrayList(10));
		
		/*@spec_public@*/ /// <summary>Whether matching should be inverted </summary>
		internal bool m_Invert;
		
		/*@spec_public@*/ /// <summary>The array of flags for whether an column is selected </summary>
		internal bool[] m_SelectFlags;
		
		/*@spec_public@*/ /// <summary>Store the maximum value permitted in the range. -1 indicates that
		/// no upper value has been set 
		/// </summary>
		internal int m_Upper = - 1;
		
		/// <summary>Default constructor. </summary>
		//@assignable this.*;
		public Range()
		{
		}
		
		/// <summary> Constructor to set initial range.
		/// 
		/// </summary>
		/// <param name="rangeList">the initial range
		/// </param>
		/// <exception cref="IllegalArgumentException">if the range list is invalid
		/// </exception>
		public Range(System.String rangeList)
		{
			
			Ranges = rangeList;
		}
		
		/// <summary> Gets whether the supplied cardinal number is included in the current
		/// range.
		/// 
		/// </summary>
		/// <param name="index">the number of interest
		/// </param>
		/// <returns> true if index is in the current range
		/// </returns>
		/// <exception cref="RuntimeException">if the upper limit of the range hasn't been defined
		/// </exception>
		//@requires m_Upper >= 0;
		//@requires 0 <= index && index < m_SelectFlags.length;
		public virtual bool isInRange(int index)
		{
			
			if (m_Upper == - 1)
			{
				throw new System.SystemException("No upper limit has been specified for range");
			}
			if (m_Invert)
			{
				return !m_SelectFlags[index];
			}
			else
			{
				return m_SelectFlags[index];
			}
		}
		
		/// <summary> Constructs a representation of the current range. Being a string
		/// representation, the numbers are based from 1.
		/// 
		/// </summary>
		/// <returns> the string representation of the current range
		/// </returns>
		public override System.String ToString()
		{
			
			if (m_RangeStrings.Count == 0)
			{
				return "Empty";
			}
			System.String result = "Strings: ";
			System.Collections.IEnumerator enu = m_RangeStrings.GetEnumerator();
			//UPGRADE_TODO: Method 'java.util.Enumeration.hasMoreElements' was converted to 'System.Collections.IEnumerator.MoveNext' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationhasMoreElements'"
			while (enu.MoveNext())
			{
				//UPGRADE_TODO: Method 'java.util.Enumeration.nextElement' was converted to 'System.Collections.IEnumerator.Current' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationnextElement'"
				result += (((System.String) enu.Current) + " ");
			}
			result += "\n";
			
			result += ("Invert: " + m_Invert + "\n");
			
			try
			{
				if (m_Upper == - 1)
				{
					throw new System.SystemException("Upper limit has not been specified");
				}
				System.String cols = null;
				for (int i = 0; i < m_SelectFlags.Length; i++)
				{
					if (isInRange(i))
					{
						if (cols == null)
						{
							cols = "Cols: " + (i + 1);
						}
						else
						{
							cols += ("," + (i + 1));
						}
					}
				}
				if (cols != null)
				{
					result += (cols + "\n");
				}
			}
			catch (System.Exception ex)
			{
				//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Throwable.getMessage' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
				result += ex.Message;
			}
			return result;
		}
		
		/// <summary> Creates a string representation of the indices in the supplied array.
		/// 
		/// </summary>
		/// <param name="indices">an array containing indices to select.
		/// Since the array will typically come from a program, indices are assumed
		/// from 0, and thus will have 1 added in the String representation.
		/// </param>
		public static System.String indicesToRangeList(int[] indices)
		{
			
			System.Text.StringBuilder rl = new System.Text.StringBuilder();
			int last = - 2;
			bool range = false;
			for (int i = 0; i < indices.Length; i++)
			{
				if (i == 0)
				{
					rl.Append(indices[i] + 1);
				}
				else if (indices[i] == last)
				{
					range = true;
				}
				else
				{
					if (range)
					{
						rl.Append('-').Append(last);
						range = false;
					}
					rl.Append(',').Append(indices[i] + 1);
				}
				last = indices[i] + 1;
			}
			if (range)
			{
				rl.Append('-').Append(last);
			}
			return rl.ToString();
		}
		
		/// <summary>Sets the flags array. </summary>
		protected internal virtual void  setFlags()
		{
			
			m_SelectFlags = new bool[m_Upper + 1];
			System.Collections.IEnumerator enu = m_RangeStrings.GetEnumerator();
			//UPGRADE_TODO: Method 'java.util.Enumeration.hasMoreElements' was converted to 'System.Collections.IEnumerator.MoveNext' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationhasMoreElements'"
			while (enu.MoveNext())
			{
				//UPGRADE_TODO: Method 'java.util.Enumeration.nextElement' was converted to 'System.Collections.IEnumerator.Current' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationnextElement'"
				System.String currentRange = (System.String) enu.Current;
				if (!isValidRange(currentRange))
				{
					throw new System.ArgumentException("Invalid range list at " + currentRange);
				}
				int start = rangeLower(currentRange);
				int end = rangeUpper(currentRange);
				for (int i = start; (i <= m_Upper) && (i <= end); i++)
				{
					m_SelectFlags[i] = true;
				}
			}
		}
		
		
		/// <summary> Translates a single string selection into it's internal 0-based equivalent
		/// 
		/// </summary>
		/// <param name="single">the string representing the selection (eg: 1 first last)
		/// </param>
		/// <returns> the number corresponding to the selected value
		/// </returns>
		protected internal virtual int rangeSingle(System.String single)
		{
			
			if (single.ToLower().Equals("first"))
			{
				return 0;
			}
			if (single.ToLower().Equals("last"))
			{
				return m_Upper;
			}
			int index = System.Int32.Parse(single) - 1;
			if (index < 0)
			{
				index = 0;
			}
			if (index > m_Upper)
			{
				index = m_Upper;
			}
			return index;
		}
		
		/// <summary> Translates a range into it's lower index.
		/// 
		/// </summary>
		/// <param name="range">the string representation of the range
		/// </param>
		/// <returns> the lower index of the range
		/// </returns>
		protected internal virtual int rangeLower(System.String range)
		{
			
			int hyphenIndex;
			if ((hyphenIndex = range.IndexOf('-')) >= 0)
			{
				return System.Math.Min(rangeLower(range.Substring(0, (hyphenIndex) - (0))), rangeLower(range.Substring(hyphenIndex + 1)));
			}
			return rangeSingle(range);
		}
		
		/// <summary> Translates a range into it's upper index. Must only be called once
		/// setUpper has been called.
		/// 
		/// </summary>
		/// <param name="range">the string representation of the range
		/// </param>
		/// <returns> the upper index of the range
		/// </returns>
		protected internal virtual int rangeUpper(System.String range)
		{
			
			int hyphenIndex;
			if ((hyphenIndex = range.IndexOf('-')) >= 0)
			{
				return System.Math.Max(rangeUpper(range.Substring(0, (hyphenIndex) - (0))), rangeUpper(range.Substring(hyphenIndex + 1)));
			}
			return rangeSingle(range);
		}
		
		/// <summary> Determines if a string represents a valid index or simple range.
		/// Examples: <code>first  last   2   first-last  first-4  4-last</code>
		/// Doesn't check that a < b for a-b
		/// 
		/// </summary>
		/// <param name="range">
		/// </param>
		/// <returns> true if the range is valid
		/// </returns>
		protected internal virtual bool isValidRange(System.String range)
		{
			
			if (range == null)
			{
				return false;
			}
			int hyphenIndex;
			if ((hyphenIndex = range.IndexOf('-')) >= 0)
			{
				if (isValidRange(range.Substring(0, (hyphenIndex) - (0))) && isValidRange(range.Substring(hyphenIndex + 1)))
				{
					return true;
				}
				return false;
			}
			if (range.ToLower().Equals("first"))
			{
				return true;
			}
			if (range.ToLower().Equals("last"))
			{
				return true;
			}
			try
			{
				int index = System.Int32.Parse(range);
				if ((index > 0) && (index <= m_Upper + 1))
				{
					return true;
				}
				return false;
			}
			catch (System.FormatException ex)
			{
				return false;
			}
		}
		
		/// <summary> Main method for testing this class.
		/// 
		/// </summary>
		/// <param name="argv">one parameter: a test range specification
		/// </param>
		//	public static void main(String [] argv) 
		//	{
		//		try 
		//		{
		//			if (argv.length == 0) 
		//			{
		//				throw new Exception("Usage: Range <rangespec>");
		//			}
		//			Range range = new Range();
		//			range.setRanges(argv[0]);
		//			range.setUpper(9);
		//			range.setInvert(false);
		//			System.out.println("Input: " + argv[0] + "\n"
		//				+ range.toString());
		//			int [] rangeIndices = range.getSelection();
		//			for (int i = 0; i < rangeIndices.length; i++)
		//				System.out.print(" " + (rangeIndices[i] + 1));
		//			System.out.println("");
		//		} 
		//		catch (Exception ex) 
		//		{
		//			System.out.println(ex.getMessage());
		//		}
		//	}
	}
}