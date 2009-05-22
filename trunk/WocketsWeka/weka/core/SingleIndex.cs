/*
*    SingleIndex.java
*    Copyright (C) 2003 University of Waikato
*
*/
using System;
namespace weka.core
{
	
	/// <summary> Class representing a single cardinal number. The number is set by a 
	/// string representation such as: <P>
	/// 
	/// <code>
	/// first
	/// last
	/// 1
	/// 3
	/// </code> <P>
	/// The number is internally converted from 1-based to 0-based (so methods that 
	/// set or get numbers not in string format should use 0-based numbers).
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.5 $
	/// </version>
#if !PocketPC
    [Serializable]
#endif
	public class SingleIndex
	{
		/// <summary> Sets the value of "last".
		/// 
		/// </summary>
		/// <param name="newUpper">the value of "last"
		/// </param>
		virtual public int Upper
		{
			//@ assignable m_Upper, m_IndexString, m_SelectedIndex;
			//@ ensures newUpper < 0 ==> m_Upper == \old(m_Upper);
			//@ ensures newUpper >= 0 ==> m_Upper == newUpper;
			
			set
			{
				
				if (value >= 0)
				{
					m_Upper = value;
					setValue();
				}
			}
			
		}
		/// <summary> Gets the selected index
		/// 
		/// </summary>
		/// <returns> the selected index
		/// </returns>
		/// <exception cref="RuntimeException">if the upper limit of the index hasn't been defined
		/// </exception>
		virtual public int Index
		{
			//@ requires m_Upper >= 0;
			//@ requires m_IndexString.length() > 0;
			//@ ensures \result == m_SelectedIndex;
			
			get
			{
				
				if (m_IndexString.Equals(""))
				{
					throw new System.SystemException("No index set");
				}
				if (m_Upper == - 1)
				{
					throw new System.SystemException("No upper limit has been specified for index");
				}
				return m_SelectedIndex;
			}
			
		}
		
		/// <summary>Record the string representation of the number </summary>
		protected internal System.String m_IndexString = "";
		
		/// <summary>The selected index </summary>
		protected internal int m_SelectedIndex = - 1;
		
		/// <summary>Store the maximum value permitted. -1 indicates that no upper
		/// value has been set 
		/// </summary>
		protected internal int m_Upper = - 1;
		
		/// <summary> Default constructor.
		/// 
		/// </summary>
		//@ assignable m_IndexString, m_SelectedIndex, m_Upper;
		//@ ensures m_SelectedIndex == -1;
		//@ ensures m_Upper == -1;
		public SingleIndex()
		{
		}
		
		/// <summary> Constructor to set initial index.
		/// 
		/// </summary>
		/// <param name="rangeList">the initial index
		/// </param>
		/// <exception cref="IllegalArgumentException">if the index is invalid
		/// </exception>
		//@ assignable m_IndexString, m_SelectedIndex, m_Upper;
		//@ ensures m_IndexString == index;
		//@ ensures m_SelectedIndex == -1;
		//@ ensures m_Upper == -1;
		public SingleIndex(System.String index)
		{
			
			setSingleIndex(index);
		}
		
		/// <summary> Gets the string representing the selected range of values
		/// 
		/// </summary>
		/// <returns> the range selection string
		/// </returns>
		//@ ensures \result == m_IndexString;
		public virtual System.String getSingleIndex()
		{
			
			return m_IndexString;
		}
		
		/// <summary> Sets the index from a string representation. Note that setUpper()
		/// must be called for the value to be actually set
		/// 
		/// </summary>
		/// <param name="index">the index set
		/// </param>
		/// <exception cref="IllegalArgumentException">if the index was not well formed
		/// </exception>
		//@ assignable m_IndexString, m_SelectedIndex;
		//@ ensures m_IndexString == index;
		//@ ensures m_SelectedIndex == -1;
		public virtual void  setSingleIndex(System.String index)
		{
			
			m_IndexString = index;
			m_SelectedIndex = - 1;
		}
		
		/// <summary> Constructs a representation of the current range. Being a string
		/// representation, the numbers are based from 1.
		/// 
		/// </summary>
		/// <returns> the string representation of the current range
		/// </returns>
		//@ also signals (RuntimeException e) \old(m_Upper) < 0;
		//@ ensures \result != null;
		public override System.String ToString()
		{
			
			if (m_IndexString.Equals(""))
			{
				return "No index set";
			}
			if (m_Upper == - 1)
			{
				throw new System.SystemException("Upper limit has not been specified");
			}
			return m_IndexString;
		}
		
		/// <summary> Creates a string representation of the given index.
		/// 
		/// </summary>
		/// <param name="indices">an array containing indices to select.
		/// Since the array will typically come from a program, indices are assumed
		/// from 0, and thus will have 1 added in the String representation.
		/// </param>
		//@ requires index >= 0;
		public static System.String indexToString(int index)
		{
			
			return "" + (index + 1);
		}
		
		/// <summary> Translates a single string selection into it's internal 0-based equivalent
		/// 
		/// </summary>
		/// <param name="single">the string representing the selection (eg: 1 first last)
		/// </param>
		/// <returns> the number corresponding to the selected value
		/// </returns>
		//@ assignable m_SelectedIndex, m_IndexString;
		protected internal virtual void  setValue()
		{
			
			if (m_IndexString.Equals(""))
			{
				throw new System.SystemException("No index set");
			}
			if (m_IndexString.ToLower().Equals("first"))
			{
				m_SelectedIndex = 0;
			}
			else if (m_IndexString.ToLower().Equals("last"))
			{
				m_SelectedIndex = m_Upper;
			}
			else
			{
				m_SelectedIndex = System.Int32.Parse(m_IndexString) - 1;
				if (m_SelectedIndex < 0)
				{
					m_IndexString = "";
					throw new System.ArgumentException("Index must be greater than zero");
				}
				if (m_SelectedIndex > m_Upper)
				{
					m_IndexString = "";
					throw new System.ArgumentException("Index is too large");
				}
			}
		}
		
		/// <summary> Main method for testing this class.
		/// 
		/// </summary>
		/// <param name="argv">one parameter: a test index specification
		/// </param>
		//@ requires \nonnullelements(argv);
		//	public static void main(/*@non_null@*/ String [] argv) 
		//	{
		//		try 
		//		{
		//			if (argv.length == 0) 
		//			{
		//				throw new Exception("Usage: SingleIndex <indexspec>");
		//			}
		//			SingleIndex singleIndex = new SingleIndex();
		//			singleIndex.setSingleIndex(argv[0]);
		//			singleIndex.setUpper(9);
		//			System.out.println("Input: " + argv[0] + "\n"
		//				+ singleIndex.toString());
		//			int selectedIndex = singleIndex.getIndex();
		//			System.out.println(selectedIndex + "");
		//		} 
		//		catch (Exception ex) 
		//		{
		//			ex.printStackTrace();
		//			System.out.println(ex.getMessage());
		//		}
		//	}
	}
}