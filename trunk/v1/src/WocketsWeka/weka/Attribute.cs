/*
*    Attribute.java
*    Copyright (C) 1999 Eibe Frank
*
*/
using System;
using System.Globalization;
using WocketsWeka.Utils;

namespace weka.core
{
	
	/// <summary> Class for handling an attribute. Once an attribute has been created,
	/// it can't be changed. <p>
	/// 
	/// The following attribute types are supported:
	/// <ul>
	/// <li> numeric: <br/>
	/// This type of attribute represents a floating-point number.
	/// </li>
	/// <li> nominal: <br/>
	/// This type of attribute represents a fixed set of nominal values.
	/// </li>
	/// <li> string: <br/>
	/// This type of attribute represents a dynamically expanding set of
	/// nominal values. Usually used in text classification.
	/// </li>
	/// <li> date: <br/>
	/// This type of attribute represents a date, internally represented as 
	/// floating-point number storing the milliseconds since January 1, 
	/// 1970, 00:00:00 GMT. The string representation of the date must be
	/// <a href="http://www.iso.org/iso/en/prods-services/popstds/datesandtime.html" target="_blank">
	/// ISO-8601</a> compliant, the default is <code>yyyy-MM-dd'T'HH:mm:ss</code>.
	/// </li>
	/// </ul>
	/// 
	/// Typical usage (code from the main() method of this class): <p>
	/// 
	/// <code>
	/// ... <br>
	/// 
	/// // Create numeric attributes "length" and "weight" <br>
	/// Attribute length = new Attribute("length"); <br>
	/// Attribute weight = new Attribute("weight"); <br><br>
	/// 
	/// // Create vector to hold nominal values "first", "second", "third" <br>
	/// FastVector my_nominal_values = new FastVector(3); <br>
	/// my_nominal_values.addElement("first"); <br>
	/// my_nominal_values.addElement("second"); <br>
	/// my_nominal_values.addElement("third"); <br><br>
	/// 
	/// // Create nominal attribute "position" <br>
	/// Attribute position = new Attribute("position", my_nominal_values);<br>
	/// 
	/// ... <br>
	/// </code><p>
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.32.2.3 $
	/// </version>
#if !PocketPC
    [Serializable]
#endif
	public class Attribute : Copyable
	{

		/// <summary> Test if the attribute is nominal.
		/// 
		/// </summary>
		/// <returns> true if the attribute is nominal
		/// </returns>
		virtual public bool Nominal
		{
			//@ ensures \result <==> (m_Type == NOMINAL);
			
			get
			{
				
				return (m_Type == NOMINAL);
			}
			
		}
		/// <summary> Tests if the attribute is numeric.
		/// 
		/// </summary>
		/// <returns> true if the attribute is numeric
		/// </returns>
		virtual public bool Numeric
		{
			//@ ensures \result <==> ((m_Type == NUMERIC) || (m_Type == DATE));
			
			get
			{
				
				return ((m_Type == NUMERIC) || (m_Type == DATE));
			}
			
		}
		/// <summary> Tests if the attribute is a string.
		/// 
		/// </summary>
		/// <returns> true if the attribute is a string
		/// </returns>
		virtual public bool String
		{
			//@ ensures \result <==> (m_Type == STRING);
			
			get
			{
				
				return (m_Type == STRING);
			}
			
		}
		/// <summary> Tests if the attribute is a date type.
		/// 
		/// </summary>
		/// <returns> true if the attribute is a date type
		/// </returns>
		virtual public bool Date
		{
			//@ ensures \result <==> (m_Type == DATE);
			
			get
			{
				
				return (m_Type == DATE);
			}
			
		}
		/// <summary> Sets the index of this attribute.
		/// 
		/// </summary>
		/// <param name="the">index of this attribute
		/// </param>
		virtual internal int Index
		{
			//@ requires 0 <= index;
			//@ assignable m_Index;
			//@ ensures m_Index == index;
			
			set
			{
				
				m_Index = value;
			}
			
		}
		/// <summary> Returns whether the attribute values are equally spaced.
		/// 
		/// </summary>
		/// <returns> whether the attribute is regular or not
		/// </returns>
		virtual public bool Regular
		{
			get
			{
				
				return m_IsRegular;
			}
			
		}
		/// <summary> Returns whether the attribute can be averaged meaningfully.
		/// 
		/// </summary>
		/// <returns> whether the attribute can be averaged or not
		/// </returns>
		virtual public bool Averagable
		{
			get
			{
				
				return m_IsAveragable;
			}
			
		}
		/// <summary> Returns the lower bound of a numeric attribute.
		/// 
		/// </summary>
		/// <returns> the lower bound of the specified numeric range
		/// </returns>
		virtual public double LowerNumericBound
		{
			get
			{
				
				return m_LowerBound;
			}
			
		}
		/// <summary> Returns the upper bound of a numeric attribute.
		/// 
		/// </summary>
		/// <returns> the upper bound of the specified numeric range
		/// </returns>
		virtual public double UpperNumericBound
		{
			get
			{
				
				return m_UpperBound;
			}
			
		}
		/// <summary> Sets the numeric range based on a string. If the string is null the range
		/// will default to [-inf,+inf]. A square brace represents a closed interval, a
		/// curved brace represents an open interval, and 'inf' represents infinity.
		/// Examples of valid range strings: "[-inf,20)","(-13.5,-5.2)","(5,inf]"
		/// 
		/// </summary>
		/// <param name="rangeString">the string to parse as the attribute's numeric range
		/// </param>
		/// <exception cref="IllegalArgumentException">if the range is not valid
		/// </exception>
		private System.String NumericRange
		{
			//@ requires rangeString != null;
			
			set
			{
				// set defaults
				m_LowerBound = System.Double.NegativeInfinity;
				m_LowerBoundIsOpen = false;
				m_UpperBound = System.Double.PositiveInfinity;
				m_UpperBoundIsOpen = false;
				
				if (value == null)
					return ;
				
				// set up a tokenzier to parse the string
				StreamTokenizer tokenizer = new StreamTokenizer(new System.IO.StringReader(value));
				tokenizer.Settings.ResetCharTypeTable();
				tokenizer.Settings.WhitespaceChars(0, (int) ' ');
				tokenizer.Settings.WordChars((int)' ' + 1, (int) '\u00FF');
				tokenizer.Settings.OrdinaryChar((int) '[');
                tokenizer.Settings.OrdinaryChar((int)'(');
                tokenizer.Settings.OrdinaryChar((int)',');
                tokenizer.Settings.OrdinaryChar((int)']');
                tokenizer.Settings.OrdinaryChar((int) ')');
				
				try
				{
					
					// get opening brace
                    Token token;
                    tokenizer.NextToken(out token);
					
					if ((token is CharToken) && (token.StringValue == "["))
                    //if (token.StringValue == '[')
						m_LowerBoundIsOpen = false;
                    else if ((token is CharToken) && (token.StringValue == "("))
						m_LowerBoundIsOpen = true;
					else
						throw new System.ArgumentException("Expected opening brace on range," + " found: " + token.StringValue);
					
					// get lower bound
                    tokenizer.NextToken(out token);
					//f (tokenizer.ttype != StreamTokenizer.TT_WORD)
                    if (!(token is WordToken))
						throw new System.ArgumentException("Expected lower bound in range," + " found: " + token.StringValue);

					if (System.String.Compare(token.StringValue, "-inf", true) == 0)
						m_LowerBound = System.Double.NegativeInfinity;
                    else if (System.String.Compare(token.StringValue, "+inf", true) == 0)
						m_LowerBound = System.Double.PositiveInfinity;
                    else if (System.String.Compare(token.StringValue, "inf", true) == 0)
						m_LowerBound = System.Double.NegativeInfinity;
					else
						try
						{
                            m_LowerBound = System.Double.Parse(token.StringValue);
						}
						catch (System.FormatException e)
						{
							throw new System.ArgumentException("Expected lower bound in range," + " found: '" + token.StringValue + "'" +" "+e.ToString());
						}
					
					// get separating comma
                    tokenizer.NextToken(out token);
					if ( token.StringValue != ",")
						throw new System.ArgumentException("Expected comma in range," + " found: " + token.StringValue);
					
					// get upper bound
                    tokenizer.NextToken(out token);
					//if (tokenizer.ttype != StreamTokenizer.TT_WORD)
                    if (!(token is WordToken))
						throw new System.ArgumentException("Expected upper bound in range," + " found: " + token.StringValue);
                    if (System.String.Compare(token.StringValue, "-inf", true) == 0)
						m_UpperBound = System.Double.NegativeInfinity;
                    else if (System.String.Compare(token.StringValue, "+inf", true) == 0)
						m_UpperBound = System.Double.PositiveInfinity;
                    else if (System.String.Compare(token.StringValue, "inf", true) == 0)
						m_UpperBound = System.Double.PositiveInfinity;
					else
						try
						{
                            m_UpperBound = System.Double.Parse(token.StringValue);
						}
						catch (System.FormatException e)
						{
                            throw new System.ArgumentException("Expected upper bound in range," + " found: '" + token.StringValue + "'" + " " + e.ToString());
						}
					
					// get closing brace
                    tokenizer.NextToken(out token);
					
					//if (tokenizer.ttype == ']')
                    if ((token is CharToken) && (token.StringValue == "]"))
						m_UpperBoundIsOpen = false;
					//else if (tokenizer.ttype == ')')
                    else if ((token is CharToken) && (token.StringValue == ")"))
						m_UpperBoundIsOpen = true;
					else
						throw new System.ArgumentException("Expected closing brace on range," + " found: " + token.StringValue);
					
					// check for rubbish on end
                    tokenizer.NextToken(out token);
					//if (tokenizer.NextToken() != StreamTokenizer.TT_EOF)
                    if (!(token is EofToken))
						throw new System.ArgumentException("Expected end of range string," + " found: " + token.StringValue);
				}
				catch (System.IO.IOException e)
				{
					//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Throwable.getMessage' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
					throw new System.ArgumentException("IOException reading attribute range" + " string: " + e.Message);
				}
				
				if (m_UpperBound < m_LowerBound)
					throw new System.ArgumentException("Upper bound (" + m_UpperBound + ") on numeric range is" + " less than lower bound (" + m_LowerBound + ")!");
			}
			
			/// <summary> Simple main method for testing this class.</summary>
			//@ requires ops != null;
			//@ requires \nonnullelements(ops);
			//	public static void main(String[] ops) 
			//	{
			//		try 
			//		{
			//      
			//			// Create numeric attributes "length" and "weight"
			//			Attribute length = new Attribute("length");
			//			Attribute weight = new Attribute("weight");
			//
			//			// Create date attribute "date"
			//			Attribute date = new Attribute("date", "yyyy-MM-dd HH:mm:ss");
			//
			//			System.out.println(date);
			//			double dd = date.parseDate("2001-04-04 14:13:55");
			//			System.out.println("Test date = " + dd);
			//			System.out.println(date.formatDate(dd));
			//
			//			dd = new Date().getTime();
			//			System.out.println("Date now = " + dd);
			//			System.out.println(date.formatDate(dd));
			//      
			//			// Create vector to hold nominal values "first", "second", "third" 
			//			FastVector my_nominal_values = new FastVector(3); 
			//			my_nominal_values.addElement("first"); 
			//			my_nominal_values.addElement("second"); 
			//			my_nominal_values.addElement("third"); 
			//      
			//			// Create nominal attribute "position" 
			//			Attribute position = new Attribute("position", my_nominal_values);
			//
			//			// Print the name of "position"
			//			System.out.println("Name of \"position\": " + position.name());
			//
			//			// Print the values of "position"
			//			Enumeration attValues = position.enumerateValues();
			//			while (attValues.hasMoreElements()) 
			//			{
			//				String string = (String)attValues.nextElement();
			//				System.out.println("Value of \"position\": " + string);
			//			}
			//
			//			// Shallow copy attribute "position"
			//			Attribute copy = (Attribute) position.copy();
			//
			//			// Test if attributes are the same
			//			System.out.println("Copy is the same as original: " + copy.equals(position));
			//
			//			// Print index of attribute "weight" (should be unset: -1)
			//			System.out.println("Index of attribute \"weight\" (should be -1): " + 
			//				weight.index());
			//
			//			// Print index of value "first" of attribute "position"
			//			System.out.println("Index of value \"first\" of \"position\" (should be 0): " +
			//				position.indexOfValue("first"));
			//
			//			// Tests type of attribute "position"
			//			System.out.println("\"position\" is numeric: " + position.isNumeric());
			//			System.out.println("\"position\" is nominal: " + position.isNominal());
			//			System.out.println("\"position\" is string: " + position.isString());
			//
			//			// Prints name of attribute "position"
			//			System.out.println("Name of \"position\": " + position.name());
			//    
			//			// Prints number of values of attribute "position"
			//			System.out.println("Number of values for \"position\": " + position.numValues());
			//
			//			// Prints the values (againg)
			//			for (int i = 0; i < position.numValues(); i++) 
			//			{
			//				System.out.println("Value " + i + ": " + position.value(i));
			//			}
			//
			//			// Prints the attribute "position" in ARFF format
			//			System.out.println(position);
			//
			//			// Checks type of attribute "position" using constants
			//			switch (position.type()) 
			//			{
			//				case Attribute.NUMERIC:
			//					System.out.println("\"position\" is numeric");
			//					break;
			//				case Attribute.NOMINAL:
			//					System.out.println("\"position\" is nominal");
			//					break;
			//				case Attribute.STRING:
			//					System.out.println("\"position\" is string");
			//					break;
			//				case Attribute.DATE:
			//					System.out.println("\"position\" is date");
			//					break;
			//				default:
			//					System.out.println("\"position\" has unknown type");
			//			}
			//		} 
			//		catch (Exception e) 
			//		{
			//			e.printStackTrace();
			//		}
			//	}
			
		}
		/// <summary>Constant set for numeric attributes. </summary>
		public const int NUMERIC = 0;
		/// <summary>Constant set for nominal attributes. </summary>
		public const int NOMINAL = 1;
		/// <summary>Constant set for attributes with string values. </summary>
		public const int STRING = 2;
		/// <summary>Constant set for attributes with date values. </summary>
		public const int DATE = 3;
		/// <summary>Constant set for symbolic attributes. </summary>
		public const int ORDERING_SYMBOLIC = 0;
		/// <summary>Constant set for ordered attributes. </summary>
		public const int ORDERING_ORDERED = 1;
		/// <summary>Constant set for modulo-ordered attributes. </summary>
		public const int ORDERING_MODULO = 2;
		/// <summary>The keyword used to denote the start of an arff attribute declaration </summary>
		internal static System.String ARFF_ATTRIBUTE = "@attribute";
		/// <summary>A keyword used to denote a numeric attribute </summary>
		internal static System.String ARFF_ATTRIBUTE_INTEGER = "integer";
		/// <summary>A keyword used to denote a numeric attribute </summary>
		internal static System.String ARFF_ATTRIBUTE_REAL = "real";
		/// <summary>A keyword used to denote a numeric attribute </summary>
		internal static System.String ARFF_ATTRIBUTE_NUMERIC = "numeric";
		/// <summary>The keyword used to denote a string attribute </summary>
		internal static System.String ARFF_ATTRIBUTE_STRING = "string";
		/// <summary>The keyword used to denote a date attribute </summary>
		internal static System.String ARFF_ATTRIBUTE_DATE = "date";
		/// <summary>Strings longer than this will be stored compressed. </summary>
		private const int STRING_COMPRESS_THRESHOLD = 200;
		/// <summary>The attribute's name. </summary>
		private System.String m_Name;
		/// <summary>The attribute's type. </summary>
		private int m_Type;
		/*@ invariant m_Type == NUMERIC || 
		m_Type == DATE || 
		m_Type == STRING || 
		m_Type == NOMINAL;
		*/
		
		/// <summary>The attribute's values (if nominal or string). </summary>
		private FastVector m_Values;
		/// <summary>Mapping of values to indices (if nominal or string). </summary>
		private System.Collections.Hashtable m_Hashtable;
		/// <summary>Date format specification for date attributes </summary>
		//UPGRADE_ISSUE: Class 'java.text.SimpleDateFormat' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javatextSimpleDateFormat'"
		private string m_DateFormat;
		/// <summary>The attribute's index. </summary>
		private int m_Index;
		/// <summary>The attribute's metadata. </summary>
		private ProtectedProperties m_Metadata;
		/// <summary>The attribute's ordering. </summary>
		private int m_Ordering;
		/// <summary>Whether the attribute is regular. </summary>
		private bool m_IsRegular;
		/// <summary>Whether the attribute is averagable. </summary>
		private bool m_IsAveragable;
		/// <summary>Whether the attribute has a zeropoint. </summary>
		private bool m_HasZeropoint;
		/// <summary>The attribute's weight. </summary>
		private double m_Weight;
		/// <summary>The attribute's lower numeric bound. </summary>
		private double m_LowerBound;
		/// <summary>Whether the lower bound is open. </summary>
		private bool m_LowerBoundIsOpen;
		/// <summary>The attribute's upper numeric bound. </summary>
		private double m_UpperBound;
		/// <summary>Whether the upper bound is open </summary>
		private bool m_UpperBoundIsOpen;
		
		/// <summary> Constructor for a numeric attribute.
		/// 
		/// </summary>
		/// <param name="attributeName">the name for the attribute
		/// </param>
		//@ requires attributeName != null;
		//@ ensures  m_Name == attributeName;
		//UPGRADE_TODO: Format of property file may need to be changed. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1089'"
		//UPGRADE_ISSUE: Class hierarchy differences between 'java.util.Properties' and 'System.Collections.Specialized.NameValueCollection' may cause compilation errors. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1186'"
		public Attribute(System.String attributeName):this(attributeName, new ProtectedProperties(new System.Collections.Specialized.NameValueCollection()))
		{
		}
		
		/// <summary> Constructor for a numeric attribute, where metadata is supplied.
		/// 
		/// </summary>
		/// <param name="attributeName">the name for the attribute
		/// </param>
		/// <param name="metadata">the attribute's properties
		/// </param>
		//@ requires attributeName != null;
		//@ requires metadata != null;
		//@ ensures  m_Name == attributeName;
		public Attribute(System.String attributeName, ProtectedProperties metadata)
		{
			
			m_Name = attributeName;
			m_Index = - 1;
			m_Values = null;
			m_Hashtable = null;
			m_Type = NUMERIC;
			setMetadata(metadata);
		}
		
		/// <summary> Constructor for a date attribute.
		/// 
		/// </summary>
		/// <param name="attributeName">the name for the attribute
		/// </param>
		/// <param name="dateFormat">a string suitable for use with
		/// SimpleDateFormatter for parsing dates.
		/// </param>
		//@ requires attributeName != null;
		//@ requires dateFormat != null;
		//@ ensures  m_Name == attributeName;
		//UPGRADE_TODO: Format of property file may need to be changed. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1089'"
		//UPGRADE_ISSUE: Class hierarchy differences between 'java.util.Properties' and 'System.Collections.Specialized.NameValueCollection' may cause compilation errors. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1186'"
		public Attribute(System.String attributeName, System.String dateFormat):this(attributeName, dateFormat, new ProtectedProperties(new System.Collections.Specialized.NameValueCollection()))
		{
		}
		
		/// <summary> Constructor for a date attribute, where metadata is supplied.
		/// 
		/// </summary>
		/// <param name="attributeName">the name for the attribute
		/// </param>
		/// <param name="dateFormat">a string suitable for use with
		/// SimpleDateFormatter for parsing dates.
		/// </param>
		/// <param name="metadata">the attribute's properties
		/// </param>
		//@ requires attributeName != null;
		//@ requires dateFormat != null;
		//@ requires metadata != null;
		//@ ensures  m_Name == attributeName;
		public Attribute(System.String attributeName, System.String dateFormat, ProtectedProperties metadata)
		{
			
			m_Name = attributeName;
			m_Index = - 1;
			m_Values = null;
			m_Hashtable = null;
			m_Type = DATE;
			if (dateFormat != null)
			{
				//UPGRADE_ISSUE: Constructor 'java.text.SimpleDateFormat.SimpleDateFormat' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javatextSimpleDateFormat'"
				m_DateFormat = dateFormat.ToString();
			}
			else
			{
				//UPGRADE_ISSUE: Constructor 'java.text.SimpleDateFormat.SimpleDateFormat' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javatextSimpleDateFormat'"
				m_DateFormat = "yyyy-MM-dd'T'HH:mm:ss";
			}
			//UPGRADE_ISSUE: Method 'java.text.DateFormat.setLenient' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javatextDateFormatsetLenient_boolean'"
			//m_DateFormat.setLenient(false);
			setMetadata(metadata);
		}
		
		/// <summary> Constructor for nominal attributes and string attributes.
		/// If a null vector of attribute values is passed to the method,
		/// the attribute is assumed to be a string.
		/// 
		/// </summary>
		/// <param name="attributeName">the name for the attribute
		/// </param>
		/// <param name="attributeValues">a vector of strings denoting the 
		/// attribute values. Null if the attribute is a string attribute.
		/// </param>
		//@ requires attributeName != null;
		//@ ensures  m_Name == attributeName;
		//UPGRADE_TODO: Format of property file may need to be changed. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1089'"
		//UPGRADE_ISSUE: Class hierarchy differences between 'java.util.Properties' and 'System.Collections.Specialized.NameValueCollection' may cause compilation errors. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1186'"
		public Attribute(System.String attributeName, FastVector attributeValues):this(attributeName, attributeValues, new ProtectedProperties(new System.Collections.Specialized.NameValueCollection()))
		{
		}
		
		/// <summary> Constructor for nominal attributes and string attributes, where
		/// metadata is supplied. If a null vector of attribute values is passed
		/// to the method, the attribute is assumed to be a string.
		/// 
		/// </summary>
		/// <param name="attributeName">the name for the attribute
		/// </param>
		/// <param name="attributeValues">a vector of strings denoting the 
		/// attribute values. Null if the attribute is a string attribute.
		/// </param>
		/// <param name="metadata">the attribute's properties
		/// </param>
		//@ requires attributeName != null;
		//@ requires metadata != null;
		/*@ ensures  m_Name == attributeName;
		ensures  m_Index == -1;
		ensures  attributeValues == null && m_Type == STRING
		|| attributeValues != null && m_Type == NOMINAL 
		&& m_Values.size() == attributeValues.size();
		signals (IllegalArgumentException ex) 
		(* if duplicate strings in attributeValues *);
		*/
		public Attribute(System.String attributeName, FastVector attributeValues, ProtectedProperties metadata)
		{
			
			m_Name = attributeName;
			m_Index = - 1;
			if (attributeValues == null)
			{
				m_Values = new FastVector();
				m_Hashtable = System.Collections.Hashtable.Synchronized(new System.Collections.Hashtable());
				m_Type = STRING;
			}
			else
			{
				m_Values = new FastVector(attributeValues.size());
				//m_Hashtable = System.Collections.Hashtable.Synchronized(new System.Collections.Hashtable(attributeValues.size()));
                m_Hashtable = new System.Collections.Hashtable(attributeValues.size());
				for (int i = 0; i < attributeValues.size(); i++)
				{
                    // No serialization
					System.Object store = attributeValues.elementAt(i);
					
                    //if (((System.String) store).Length > STRING_COMPRESS_THRESHOLD)
					//{
					//	try
					//	{
					//		store = new SerializedObject(attributeValues.elementAt(i), true);
					//	}
					//	catch (System.Exception ex)
					//	{
					//		System.Console.Error.WriteLine("Couldn't compress nominal attribute value -" + " storing uncompressed.");
					//	}
					//}

					if (m_Hashtable.ContainsKey(store))
					{
						//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Object.toString' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
						throw new System.ArgumentException("A nominal attribute (" + attributeName + ") cannot" + " have duplicate labels (" + store + ").");
					}
					m_Values.addElement(store);
                    m_Hashtable.Add(store, (System.Int32) i);

				}
				m_Type = NOMINAL;
			}
			setMetadata(metadata);
		}
		
		/// <summary> Produces a shallow copy of this attribute.
		/// 
		/// </summary>
		/// <returns> a copy of this attribute with the same index
		/// </returns>
		//@ also ensures \result instanceof Attribute;
		public virtual System.Object copy()
		{
			
			Attribute copy = new Attribute(m_Name);
			
			copy.m_Index = m_Index;
			copy.m_Type = m_Type;
			copy.m_Values = m_Values;
			copy.m_Hashtable = m_Hashtable;
			copy.m_DateFormat = m_DateFormat;
			copy.setMetadata(m_Metadata);
			
			return copy;
		}




		/// <summary> Returns an enumeration of all the attribute's values if
		/// the attribute is nominal or a string, null otherwise. 
		/// 
		/// </summary>
		/// <returns> enumeration of all the attribute's values
		/// </returns>
		public System.Collections.IEnumerator enumerateValues()
		{
			
			if (Nominal || String)
			{
				//UPGRADE_NOTE: Final was removed from the declaration of 'ee '. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1003'"
				//System.Collections.IEnumerator ee = m_Values.elements();
                return new FastVectorEnumeration(m_Values);
			}
			return null;
		}
		
		/// <summary> Tests if given attribute is equal to this attribute.
		/// 
		/// </summary>
		/// <param name="other">the Object to be compared to this attribute
		/// </param>
		/// <returns> true if the given attribute is equal to this attribute
		/// </returns>
		public  override bool Equals(System.Object other)
		{
			
			if ((other == null) || !(other.GetType().Equals(this.GetType())))
			{
				return false;
			}
			Attribute att = (Attribute) other;
			if (!m_Name.Equals(att.m_Name))
			{
				return false;
			}
			if (Nominal && att.Nominal)
			{
				if (m_Values.size() != att.m_Values.size())
				{
					return false;
				}
				for (int i = 0; i < m_Values.size(); i++)
				{
					if (!m_Values.elementAt(i).Equals(att.m_Values.elementAt(i)))
					{
						return false;
					}
				}
				return true;
			}
			else
			{
				return (type() == att.type());
			}
		}
		
		/// <summary> Returns the index of this attribute.
		/// 
		/// </summary>
		/// <returns> the index of this attribute
		/// </returns>
		//@ ensures \result == m_Index;
		public int index()
		{
			
			return m_Index;
		}
		
		/// <summary> Returns the index of a given attribute value. (The index of
		/// the first occurence of this value.)
		/// 
		/// </summary>
		/// <param name="value">the value for which the index is to be returned
		/// </param>
		/// <returns> the index of the given attribute value if attribute
		/// is nominal or a string, -1 if it is numeric or the value 
		/// can't be found
		/// </returns>
		public int indexOfValue(System.String value_Renamed)
		{
			
			if (!Nominal && !String)
				return - 1;
			System.Object store = value_Renamed;
			if (value_Renamed.Length > STRING_COMPRESS_THRESHOLD)
			{
				try
				{
					store = value_Renamed;
				}
				catch (System.Exception ex)
				{
					System.Console.Error.WriteLine("Couldn't compress string attribute value -" + " searching uncompressed." + " "+ex.ToString());
				}
			}
			
			//UPGRADE_TODO: The 'System.Int32' structure does not have an equivalent to NULL. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1291'"
			if (m_Hashtable.ContainsKey(store))
				return (System.Int32) m_Hashtable[store];
			else
				return -1;
		}
		
		/// <summary> Returns the attribute's name.
		/// 
		/// </summary>
		/// <returns> the attribute's name as a string
		/// </returns>
		//@ ensures \result == m_Name;
		public System.String name()
		{
			
			return m_Name;
		}
		
		/// <summary> Returns the number of attribute values. Returns 0 for numeric attributes.
		/// 
		/// </summary>
		/// <returns> the number of attribute values
		/// </returns>
		public int numValues()
		{
			
			if (!Nominal && !String)
			{
				return 0;
			}
			else
			{
				return m_Values.size();
			}
		}
		
		/// <summary> Returns a description of this attribute in ARFF format. Quotes
		/// strings if they contain whitespace characters, or if they
		/// are a question mark.
		/// 
		/// </summary>
		/// <returns> a description of this attribute as a string
		/// </returns>
		public override System.String ToString()
		{
			
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			
			text.Append(ARFF_ATTRIBUTE).Append(" ").Append(Utils.quote(m_Name)).Append(" ");
			switch (m_Type)
			{
				
				case NOMINAL: 
					text.Append('{');
					System.Collections.IEnumerator enu = enumerateValues();
                    int countValues = 0;
					//UPGRADE_TODO: Method 'java.util.Enumeration.hasMoreElements' was converted to 'System.Collections.IEnumerator.MoveNext' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationhasMoreElements'"
                    while (enu.MoveNext())
                    {
                        //UPGRADE_TODO: Method 'java.util.Enumeration.nextElement' was converted to 'System.Collections.IEnumerator.Current' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationnextElement'"
                        text.Append(Utils.quote((System.String)enu.Current));
                        //UPGRADE_TODO: Method 'java.util.Enumeration.hasMoreElements' was converted to 'System.Collections.IEnumerator.MoveNext' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationhasMoreElements'"
                        if (countValues < this.numValues()-1)
                            text.Append(',');
                        countValues++;
                    }
					text.Append('}');
					break;
				
				case NUMERIC: 
					text.Append(ARFF_ATTRIBUTE_NUMERIC);
					break;
				
				case STRING: 
					text.Append(ARFF_ATTRIBUTE_STRING);
					break;
				
				case DATE: 
					//UPGRADE_ISSUE: Method 'java.text.SimpleDateFormat.toPattern' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javatextSimpleDateFormat'"
					text.Append(ARFF_ATTRIBUTE_DATE).Append(" ").Append(Utils.quote(m_DateFormat));
					break;
				
				default: 
					text.Append("UNKNOWN");
					break;
				
			}
			return text.ToString();
		}
		
		/// <summary> Returns the attribute's type as an integer.
		/// 
		/// </summary>
		/// <returns> the attribute's type.
		/// </returns>
		//@ ensures \result == m_Type;
		public int type()
		{
			
			return m_Type;
		}
		
		/// <summary> Returns a value of a nominal or string attribute. 
		/// Returns an empty string if the attribute is neither
		/// nominal nor a string attribute.
		/// 
		/// </summary>
		/// <param name="valIndex">the value's index
		/// </param>
		/// <returns> the attribute's value as a string
		/// </returns>
		public System.String value_Renamed(int valIndex)
		{
			
			if (!Nominal && !String)
			{
				return "";
			}
			else
			{
				System.Object val = m_Values.elementAt(valIndex);
				
				// If we're storing strings compressed, uncompress it.
				
				return (System.String) val;
			}
		}
		
		/// <summary> Constructor for a numeric attribute with a particular index.
		/// 
		/// </summary>
		/// <param name="attributeName">the name for the attribute
		/// </param>
		/// <param name="index">the attribute's index
		/// </param>
		//@ requires attributeName != null;
		//@ requires index >= 0;
		//@ ensures  m_Name == attributeName;
		//@ ensures  m_Index == index;
		internal Attribute(System.String attributeName, int index):this(attributeName)
		{
			m_Index = index;
		}
		
		/// <summary> Constructor for date attributes with a particular index.
		/// 
		/// </summary>
		/// <param name="attributeName">the name for the attribute
		/// </param>
		/// <param name="dateFormat">a string suitable for use with
		/// SimpleDateFormatter for parsing dates.  Null for a default format
		/// string.
		/// </param>
		/// <param name="index">the attribute's index
		/// </param>
		//@ requires attributeName != null;
		//@ requires index >= 0;
		//@ ensures  m_Name == attributeName;
		//@ ensures  m_Index == index;
		internal Attribute(System.String attributeName, System.String dateFormat, int index):this(attributeName, dateFormat)
		{
			m_Index = index;
		}
		
		/// <summary> Constructor for nominal attributes and string attributes with
		/// a particular index.
		/// If a null vector of attribute values is passed to the method,
		/// the attribute is assumed to be a string.
		/// 
		/// </summary>
		/// <param name="attributeName">the name for the attribute
		/// </param>
		/// <param name="attributeValues">a vector of strings denoting the attribute values.
		/// Null if the attribute is a string attribute.
		/// </param>
		/// <param name="index">the attribute's index
		/// </param>
		//@ requires attributeName != null;
		//@ requires index >= 0;
		//@ ensures  m_Name == attributeName;
		//@ ensures  m_Index == index;
		internal Attribute(System.String attributeName, FastVector attributeValues, int index):this(attributeName, attributeValues)
		{
			m_Index = index;
		}
		
		/// <summary> Adds a string value to the list of valid strings for attributes
		/// of type STRING and returns the index of the string.
		/// 
		/// </summary>
		/// <param name="value">The string value to add
		/// </param>
		/// <returns> the index assigned to the string, or -1 if the attribute is not
		/// of type Attribute.STRING 
		/// </returns>
		/*@ requires value != null;
		ensures  isString() && 0 <= \result && \result < m_Values.size() ||
		! isString() && \result == -1;
		*/
		public virtual int addStringValue(System.String value_Renamed)
		{
			
			if (!String)
			{
				return - 1;
			}
			System.Object store = value_Renamed;
			
			if (value_Renamed.Length > STRING_COMPRESS_THRESHOLD)
			{
			
			    store = value_Renamed;
				
			}
			
			//UPGRADE_TODO: The 'System.Int32' structure does not have an equivalent to NULL. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1291'"
			if (m_Hashtable.ContainsKey(store))
			{
				return (System.Int32) m_Hashtable[store];
			}
			else
			{
				int intIndex = m_Values.size();
				m_Values.addElement(store);				
				m_Hashtable.Add(store, (System.Int32) intIndex);				
				return intIndex;
			}
		}
		
		/// <summary> Adds a string value to the list of valid strings for attributes
		/// of type STRING and returns the index of the string. This method is
		/// more efficient than addStringValue(String) for long strings.
		/// 
		/// </summary>
		/// <param name="src">The Attribute containing the string value to add.
		/// </param>
		/// <param name="int">index the index of the string value in the source attribute.
		/// </param>
		/// <returns> the index assigned to the string, or -1 if the attribute is not
		/// of type Attribute.STRING 
		/// </returns>
		/*@ requires src != null;
		requires 0 <= index && index < src.m_Values.size();
		ensures  isString() && 0 <= \result && \result < m_Values.size() ||
		! isString() && \result == -1;
		*/
		public virtual int addStringValue(Attribute src, int index)
		{
			
			if (!String)
			{
				return - 1;
			}
			System.Object store = src.m_Values.elementAt(index);
		
			//UPGRADE_TODO: The 'System.Int32' structure does not have an equivalent to NULL. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1291'"
			if (m_Hashtable.ContainsKey(store))
			{
				return (System.Int32) m_Hashtable[store];
			}
			else
			{
				int intIndex = m_Values.size();
				m_Values.addElement(store);
				m_Hashtable.Add(store, (System.Int32) intIndex);
				return intIndex;
			}
		}
		
		/// <summary> Adds an attribute value. Creates a fresh list of attribute
		/// values before adding it.
		/// 
		/// </summary>
		/// <param name="value">the attribute value
		/// </param>
		internal void  addValue(System.String value_Renamed)
		{
			
			m_Values = (FastVector) m_Values.copy();
			m_Hashtable = (System.Collections.Hashtable) m_Hashtable.Clone();
			forceAddValue(value_Renamed);
		}
		
		/// <summary> Produces a shallow copy of this attribute with a new name.
		/// 
		/// </summary>
		/// <param name="newName">the name of the new attribute
		/// </param>
		/// <returns> a copy of this attribute with the same index
		/// </returns>
		//@ requires newName != null;
		//@ ensures \result.m_Name  == newName;
		//@ ensures \result.m_Index == m_Index;
		//@ ensures \result.m_Type  == m_Type;
		internal Attribute copy(System.String newName)
		{
			
			Attribute copy = new Attribute(newName);
			
			copy.m_Index = m_Index;
			copy.m_DateFormat = m_DateFormat;
			copy.m_Type = m_Type;
			copy.m_Values = m_Values;
			copy.m_Hashtable = m_Hashtable;
			copy.setMetadata(m_Metadata);
			
			return copy;
		}
		
		/// <summary> Removes a value of a nominal or string attribute. Creates a 
		/// fresh list of attribute values before removing it.
		/// 
		/// </summary>
		/// <param name="index">the value's index
		/// </param>
		/// <exception cref="IllegalArgumentException">if the attribute is not nominal
		/// </exception>
		//@ requires isNominal() || isString();
		//@ requires 0 <= index && index < m_Values.size();
		internal void  delete(int index)
		{
			
			if (!Nominal && !String)
				throw new System.ArgumentException("Can only remove value of" + "nominal or string attribute!");
			else
			{
				m_Values = (FastVector) m_Values.copy();
				m_Values.removeElementAt(index);
				System.Collections.Hashtable hash = new System.Collections.Hashtable(m_Hashtable.Count);
				System.Collections.IEnumerator enu = m_Hashtable.Keys.GetEnumerator();
				//UPGRADE_TODO: Method 'java.util.Enumeration.hasMoreElements' was converted to 'System.Collections.IEnumerator.MoveNext' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationhasMoreElements'"
				while (enu.MoveNext())
				{
					//UPGRADE_TODO: Method 'java.util.Enumeration.nextElement' was converted to 'System.Collections.IEnumerator.Current' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationnextElement'"
					System.Object string_Renamed = enu.Current;
					System.Int32 valIndexObject = (System.Int32) m_Hashtable[string_Renamed];
					int valIndex = valIndexObject;
					if (valIndex > index)
					{
						hash.Add(string_Renamed, (System.Int32) (valIndex - 1));
						
					}
					else if (valIndex < index)
					{
						hash.Add(string_Renamed, valIndexObject);
					}
				}
				m_Hashtable = hash;
			}
		}
		
		/// <summary> Adds an attribute value.
		/// 
		/// </summary>
		/// <param name="value">the attribute value
		/// </param>
		//@ requires value != null;
		//@ ensures  m_Values.size() == \old(m_Values.size()) + 1;
		internal void  forceAddValue(System.String value_Renamed)
		{
			
			System.Object store = value_Renamed;
			if (value_Renamed.Length > STRING_COMPRESS_THRESHOLD)
			{
				try
				{
					store = value_Renamed;
				}
				catch (System.Exception ex)
				{
					System.Console.Error.WriteLine("Couldn't compress string attribute value -" + " storing uncompressed."+ " "+ex.ToString());
				}
			}
			m_Values.addElement(store);
			m_Hashtable.Add(store, (System.Int32) (m_Values.size() - 1));
			
		}
		
		/// <summary> Sets a value of a nominal attribute or string attribute.
		/// Creates a fresh list of attribute values before it is set.
		/// 
		/// </summary>
		/// <param name="index">the value's index
		/// </param>
		/// <param name="string">the value
		/// </param>
		/// <exception cref="IllegalArgumentException">if the attribute is not nominal or 
		/// string.
		/// </exception>
		//@ requires string != null;
		//@ requires isNominal() || isString();
		//@ requires 0 <= index && index < m_Values.size();
		internal void  setValue(int index, System.String string_Renamed)
		{
			
			switch (m_Type)
			{
				
				case NOMINAL: 
				case STRING: 
					m_Values = (FastVector) m_Values.copy();
					m_Hashtable = (System.Collections.Hashtable) m_Hashtable.Clone();
					System.Object store = string_Renamed;
					if (string_Renamed.Length > STRING_COMPRESS_THRESHOLD)
					{
						try
						{
							store = string_Renamed;
						}
						catch (System.Exception ex)
						{
                            System.Console.Error.WriteLine("Couldn't compress string attribute value -" + " storing uncompressed." + " " + ex.ToString());
						}
					}
					m_Hashtable.Remove(m_Values.elementAt(index));					
					m_Values.setXmlElementAt(store, index);
					m_Hashtable.Add(store, (System.Int32) index);
					
					break;
				
				default: 
					throw new System.ArgumentException("Can only set values for nominal" + " or string attributes!");
				
			}
		}
		
		//@ requires isDate();
		public virtual System.String formatDate(double date)
		{
			switch (m_Type)
			{
				
				case DATE: 
					//UPGRADE_TODO: Constructor 'java.util.Date.Date' was converted to 'System.DateTime.DateTime' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilDateDate_long'"
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					return  new System.DateTime((long) date).ToString(m_DateFormat);
				
				default: 
					throw new System.ArgumentException("Can only format date values for date" + " attributes!");
				
			}
		}
		
		//@ requires isDate();
		//@ requires string != null;
		public virtual double parseDate(System.String string_Renamed)
		{
			switch (m_Type)
			{
				
				case DATE: 
					//UPGRADE_TODO: Method 'java.util.Date.getTime' was converted to 'System.DateTime.Ticks' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilDategetTime'"
                    CultureInfo ci = new CultureInfo("en");
					long time = System.DateTime.ParseExact(string_Renamed,m_DateFormat,ci).Ticks;
					// TODO put in a safety check here if we can't store the value in a double.
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					return (double) time;
				
				default: 
					throw new System.ArgumentException("Can only parse date values for date" + " attributes!");
				
			}
		}
		
		/// <summary> Returns the properties supplied for this attribute.
		/// 
		/// </summary>
		/// <returns> metadata for this attribute
		/// </returns>
		public ProtectedProperties getMetadata()
		{
			
			return m_Metadata;
		}
		
		/// <summary> Returns the ordering of the attribute. One of the following:
		/// 
		/// ORDERING_SYMBOLIC - attribute values should be treated as symbols.
		/// ORDERING_ORDERED  - attribute values have a global ordering.
		/// ORDERING_MODULO   - attribute values have an ordering which wraps.
		/// 
		/// </summary>
		/// <returns> the ordering type of the attribute
		/// </returns>
		public int ordering()
		{
			
			return m_Ordering;
		}
		
		/// <summary> Returns whether the attribute has a zeropoint and may be
		/// added meaningfully.
		/// 
		/// </summary>
		/// <returns> whether the attribute has a zeropoint or not
		/// </returns>
		public bool hasZeropoint()
		{
			
			return m_HasZeropoint;
		}
		
		/// <summary> Returns the attribute's weight.
		/// 
		/// </summary>
		/// <returns> the attribute's weight as a double
		/// </returns>
		public double weight()
		{
			
			return m_Weight;
		}
		
		/// <summary> Returns whether the lower numeric bound of the attribute is open.
		/// 
		/// </summary>
		/// <returns> whether the lower numeric bound is open or not (closed)
		/// </returns>
		public bool lowerNumericBoundIsOpen()
		{
			
			return m_LowerBoundIsOpen;
		}
		
		/// <summary> Returns whether the upper numeric bound of the attribute is open.
		/// 
		/// </summary>
		/// <returns> whether the upper numeric bound is open or not (closed)
		/// </returns>
		public bool upperNumericBoundIsOpen()
		{
			
			return m_UpperBoundIsOpen;
		}
		
		/// <summary> Determines whether a value lies within the bounds of the attribute.
		/// 
		/// </summary>
		/// <returns> whether the value is in range
		/// </returns>
		public bool isInRange(double value_Renamed)
		{
			
			// dates and missing values are a special case 
			if (m_Type == DATE || value_Renamed == Instance.missingValue())
				return true;
			if (m_Type != NUMERIC)
			{
				// do label range check
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				int intVal = (int) value_Renamed;
				if (intVal < 0 || intVal >= m_Hashtable.Count)
					return false;
			}
			else
			{
				// do numeric bounds check
				if (m_LowerBoundIsOpen)
				{
					if (value_Renamed <= m_LowerBound)
						return false;
				}
				else
				{
					if (value_Renamed < m_LowerBound)
						return false;
				}
				if (m_UpperBoundIsOpen)
				{
					if (value_Renamed >= m_UpperBound)
						return false;
				}
				else
				{
					if (value_Renamed > m_UpperBound)
						return false;
				}
			}
			return true;
		}
		
		/// <summary> Sets the metadata for the attribute. Processes the strings stored in the
		/// metadata of the attribute so that the properties can be set up for the
		/// easy-access metadata methods. Any strings sought that are omitted will
		/// cause default values to be set.
		/// 
		/// The following properties are recognised:
		/// ordering, averageable, zeropoint, regular, weight, and range.
		/// 
		/// All other properties can be queried and handled appropriately by classes
		/// calling the getMetadata() method.
		/// 
		/// </summary>
		/// <param name="metadata">the metadata
		/// </param>
		/// <exception cref="IllegalArgumentException">if the properties are not consistent
		/// </exception>
		//@ requires metadata != null;
		private void  setMetadata(ProtectedProperties metadata)
		{
			
			m_Metadata = metadata;
			
			if (m_Type == DATE)
			{
				m_Ordering = ORDERING_ORDERED;
				m_IsRegular = true;
				m_IsAveragable = false;
				m_HasZeropoint = false;
			}
			else
			{
				
				// get ordering
				System.String orderString = m_Metadata["ordering"] == null?"":m_Metadata["ordering"];
				
				// numeric ordered attributes are averagable and zeropoint by default
				System.String def;
				if (m_Type == NUMERIC && (System.String.CompareOrdinal(orderString, "modulo") != 0) && (System.String.CompareOrdinal(orderString, "symbolic") != 0))
					def = "true";
				else
					def = "false";
				
				// determine boolean states
                m_IsAveragable = (System.String.CompareOrdinal(m_Metadata["averageable"] == null ? def : m_Metadata["averageable"], "true") == 0);
                m_HasZeropoint = (System.String.CompareOrdinal(m_Metadata["zeropoint"] == null ? def : m_Metadata["zeropoint"], "true") == 0);
				// averagable or zeropoint implies regular
				if (m_IsAveragable || m_HasZeropoint)
					def = "true";
				m_IsRegular = (System.String.CompareOrdinal(m_Metadata["regular"] == null?def:m_Metadata["regular"], "true") == 0);
				
				// determine ordering
				if (System.String.CompareOrdinal(orderString, "symbolic") == 0)
					m_Ordering = ORDERING_SYMBOLIC;
                else if (System.String.CompareOrdinal(orderString, "ordered") == 0)
					m_Ordering = ORDERING_ORDERED;
                else if (System.String.CompareOrdinal(orderString, "modulo") == 0)
					m_Ordering = ORDERING_MODULO;
				else
				{
					if (m_Type == NUMERIC || m_IsAveragable || m_HasZeropoint)
						m_Ordering = ORDERING_ORDERED;
					else
						m_Ordering = ORDERING_SYMBOLIC;
				}
			}
			
			// consistency checks
			if (m_IsAveragable && !m_IsRegular)
				throw new System.ArgumentException("An averagable attribute must be" + " regular");
			if (m_HasZeropoint && !m_IsRegular)
				throw new System.ArgumentException("A zeropoint attribute must be" + " regular");
			if (m_IsRegular && m_Ordering == ORDERING_SYMBOLIC)
				throw new System.ArgumentException("A symbolic attribute cannot be" + " regular");
			if (m_IsAveragable && m_Ordering != ORDERING_ORDERED)
				throw new System.ArgumentException("An averagable attribute must be" + " ordered");
			if (m_HasZeropoint && m_Ordering != ORDERING_ORDERED)
				throw new System.ArgumentException("A zeropoint attribute must be" + " ordered");
			
			// determine weight
			m_Weight = 1.0;
			System.String weightString = m_Metadata.Get("weight");
			if (weightString != null)
			{
				try
				{
					m_Weight = System.Double.Parse(weightString);
				}
				catch (System.FormatException e)
				{
					// Check if value is really a number
                    throw new System.ArgumentException("Not a valid attribute weight: '" + weightString + "'" + " " + e.ToString());
				}
			}
			
			// determine numeric range
			if (m_Type == NUMERIC)
				NumericRange = m_Metadata.Get("range");
		}
		//UPGRADE_NOTE: The following method implementation was automatically added to preserve functionality. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1306'"
		public override int GetHashCode()
		{
			return base.GetHashCode();
		}
	}
}