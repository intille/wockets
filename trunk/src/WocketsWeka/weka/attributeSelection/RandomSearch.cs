/*
*    This program is free software; you can redistribute it and/or modify
*    it under the terms of the GNU General Public License as published by
*    the Free Software Foundation; either version 2 of the License, or
*    (at your option) any later version.
*
*    This program is distributed in the hope that it will be useful,
*    but WITHOUT ANY WARRANTY; without even the implied warranty of
*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
*    GNU General Public License for more details.
*
*    You should have received a copy of the GNU General Public License
*    along with this program; if not, write to the Free Software
*    Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
*/

/*
*    RandomSearch.java
*    Copyright (C) 1999 Mark Hall
*
*/
using System;
//UPGRADE_TODO: The package 'weka.core' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using weka.core;
namespace weka.attributeSelection
{
	
	/// <summary> Class for performing a random search. <p>
	/// 
	/// Valid options are: <p>
	/// 
	/// -P <start set> <br>
	/// Specify a starting set of attributes. Eg 1,4,7-9. <p>
	/// 
	/// -F <percent) <br>
	/// Percentage of the search space to consider. (default = 25). <p>
	/// 
	/// -V <br>
	/// Verbose output. Output new best subsets as the search progresses. <p>
	/// 
	/// </summary>
	/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.12 $
	/// </version>
	[Serializable]
	public class RandomSearch:ASSearch, StartSetHandler, OptionHandler
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the current settings of RandomSearch.</summary>
		/// <returns> an array of strings suitable for passing to setOptions()
		/// </returns>
		/// <summary> Parses a given list of options.
		/// 
		/// Valid options are: <p>
		/// 
		/// -P <start set> <br>
		/// Specify a starting set of attributes. Eg 1,4,7-9. <p>
		/// 
		/// -F <percent) <br>
		/// Percentage of the search space to consider. (default = 25). <p>
		/// 
		/// -V <br>
		/// Verbose output. Output new best subsets as the search progresses. <p>
		/// 
		/// </summary>
		/// <param name="options">the list of options as an array of strings
		/// </param>
		/// <exception cref="Exception">if an option is not supported
		/// 
		/// 
		/// </exception>
		virtual public System.String[] Options
		{
			get
			{
				System.String[] options = new System.String[5];
				int current = 0;
				
				if (m_verbose)
				{
					options[current++] = "-V";
				}
				
				if (!(StartSet.Equals("")))
				{
					options[current++] = "-P";
					options[current++] = "" + startSetToString();
				}
				
				options[current++] = "-F";
				options[current++] = "" + m_searchSize;
				
				while (current < options.Length)
				{
					options[current++] = "";
				}
				
				return options;
			}
			
			set
			{
				System.String optionString;
				resetOptions();
				
				optionString = Utils.getOption('P', value);
				if (optionString.Length != 0)
				{
					StartSet = optionString;
				}
				
				optionString = Utils.getOption('F', value);
				if (optionString.Length != 0)
				{
					//UPGRADE_TODO: The differences in the format  of parameters for constructor 'java.lang.Double.Double'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
					SearchPercent = (System.Double.Parse(optionString));
				}
				
				Verbose = Utils.getFlag('V', value);
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Returns a list of attributes (and or attribute ranges) as a String</summary>
		/// <returns> a list of attributes (and or attribute ranges)
		/// </returns>
		/// <summary> Sets a starting set of attributes for the search. It is the
		/// search method's responsibility to report this start set (if any)
		/// in its toString() method.
		/// </summary>
		/// <param name="startSet">a string containing a list of attributes (and or ranges),
		/// eg. 1,2,6,10-15. "" indicates no start point.
		/// If a start point is supplied, random search evaluates the
		/// start point and then looks for subsets that are as good as or better 
		/// than the start point with the same or lower cardinality.
		/// </param>
		/// <exception cref="Exception">if start set can't be set.
		/// </exception>
		virtual public System.String StartSet
		{
			get
			{
				return m_startRange.Ranges;
			}
			
			set
			{
				m_startRange.Ranges=value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> get whether or not output is verbose</summary>
		/// <returns> true if output is set to verbose
		/// </returns>
		/// <summary> set whether or not to output new best subsets as the search proceeds</summary>
		/// <param name="v">true if output is to be verbose
		/// </param>
		virtual public bool Verbose
		{
			get
			{
				return m_verbose;
			}
			
			set
			{
				m_verbose = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> get the percentage of the search space to consider</summary>
		/// <returns> the percent of the search space explored
		/// </returns>
		/// <summary> set the percentage of the search space to consider</summary>
		/// <param name="p">percent of the search space ( 0 < p <= 100)
		/// </param>
		virtual public double SearchPercent
		{
			get
			{
				return m_searchSize;
			}
			
			set
			{
				value = System.Math.Abs(value);
				if (value == 0)
				{
					value = 25;
				}
				
				if (value > 100.0)
				{
					value = 100;
				}
				
				m_searchSize = (value / 100.0);
			}
			
		}
		
		/// <summary> holds a starting set as an array of attributes.</summary>
		private int[] m_starting;
		
		/// <summary>holds the start set as a range </summary>
		private Range m_startRange;
		
		/// <summary>the best feature set found during the search </summary>
		private System.Collections.BitArray m_bestGroup;
		
		/// <summary>the merit of the best subset found </summary>
		private double m_bestMerit;
		
		/// <summary> only accept a feature set as being "better" than the best if its
		/// merit is better or equal to the best, and it contains fewer
		/// features than the best (this allows LVF to be implimented).
		/// </summary>
		private bool m_onlyConsiderBetterAndSmaller;
		
		/// <summary>does the data have a class </summary>
		private bool m_hasClass;
		
		/// <summary>holds the class index </summary>
		private int m_classIndex;
		
		/// <summary>number of attributes in the data </summary>
		private int m_numAttribs;
		
		/// <summary>seed for random number generation </summary>
		private int m_seed;
		
		/// <summary>percentage of the search space to consider </summary>
		private double m_searchSize;
		
		/// <summary>the number of iterations performed </summary>
		private int m_iterations;
		
		/// <summary>random number object </summary>
		private System.Random m_random;
		
		/// <summary>output new best subsets as the search progresses </summary>
		private bool m_verbose;
		
		/// <summary> Returns a string describing this search method</summary>
		/// <returns> a description of the search suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String globalInfo()
		{
			return "RandomSearch : \n\nPerforms a Random search in " + "the space of attribute subsets. If no start set is supplied, Random " + "search starts from a random point and reports the best subset found. " + "If a start set is supplied, Random searches randomly for subsets " + "that are as good or better than the start point with the same or " + "or fewer attributes. Using RandomSearch in conjunction with a start " + "set containing all attributes equates to the LVF algorithm of Liu " + "and Setiono (ICML-96).\n";
		}
		
		/// <summary> Constructor</summary>
		public RandomSearch()
		{
			resetOptions();
		}
		
		/// <summary> Returns an enumeration describing the available options.</summary>
		/// <returns> an enumeration of all the available options.
		/// 
		/// </returns>
		public virtual System.Collections.IEnumerator listOptions()
		{
			System.Collections.ArrayList newVector = System.Collections.ArrayList.Synchronized(new System.Collections.ArrayList(3));
			
			newVector.Add(new Option("\tSpecify a starting set of attributes." + "\n\tEg. 1,3,5-7." + "\n\tIf a start point is supplied," + "\n\trandom search evaluates the start" + "\n\tpoint and then randomly looks for" + "\n\tsubsets that are as good as or better" + "\n\tthan the start point with the same" + "\n\tor lower cardinality.", "P", 1, "-P <start set>"));
			
			newVector.Add(new Option("\tPercent of search space to consider." + "\n\t(default = 25%).", "F", 1, "-F <percent> "));
			newVector.Add(new Option("\tOutput subsets as the search progresses." + "\n\t(default = false).", "V", 0, "-V"));
			return newVector.GetEnumerator();
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String startSetTipText()
		{
			return "Set the start point for the search. This is specified as a comma " + "seperated list off attribute indexes starting at 1. It can include " + "ranges. Eg. 1,2,5-9,17. If specified, Random searches for subsets " + "of attributes that are as good as or better than the start set with " + "the same or lower cardinality.";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String verboseTipText()
		{
			return "Print progress information. Sends progress info to the terminal " + "as the search progresses.";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String searchPercentTipText()
		{
			return "Percentage of the search space to explore.";
		}
		
		/// <summary> converts the array of starting attributes to a string. This is
		/// used by getOptions to return the actual attributes specified
		/// as the starting set. This is better than using m_startRanges.getRanges()
		/// as the same start set can be specified in different ways from the
		/// command line---eg 1,2,3 == 1-3. This is to ensure that stuff that
		/// is stored in a database is comparable.
		/// </summary>
		/// <returns> a comma seperated list of individual attribute numbers as a String
		/// </returns>
		private System.String startSetToString()
		{
			System.Text.StringBuilder FString = new System.Text.StringBuilder();
			bool didPrint;
			
			if (m_starting == null)
			{
				return StartSet;
			}
			
			for (int i = 0; i < m_starting.Length; i++)
			{
				didPrint = false;
				
				if ((m_hasClass == false) || (m_hasClass == true && i != m_classIndex))
				{
					FString.Append((m_starting[i] + 1));
					didPrint = true;
				}
				
				if (i == (m_starting.Length - 1))
				{
					FString.Append("");
				}
				else
				{
					if (didPrint)
					{
						FString.Append(",");
					}
				}
			}
			
			return FString.ToString();
		}
		
		/// <summary> prints a description of the search</summary>
		/// <returns> a description of the search as a string
		/// </returns>
		public override System.String ToString()
		{
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			
			text.Append("\tRandom search.\n\tStart set: ");
			if (m_starting == null)
			{
				text.Append("no attributes\n");
			}
			else
			{
				text.Append(startSetToString() + "\n");
			}
			text.Append("\tNumber of iterations: " + m_iterations + " (" + (m_searchSize * 100.0) + "% of the search space)\n");
			text.Append("\tMerit of best subset found: " + Utils.doubleToString(System.Math.Abs(m_bestMerit), 8, 3) + "\n");
			
			return text.ToString();
		}
		
		/// <summary> Searches the attribute subset space randomly.
		/// 
		/// </summary>
		/// <param name="ASEvaluator">the attribute evaluator to guide the search
		/// </param>
		/// <param name="data">the training instances.
		/// </param>
		/// <returns> an array (not necessarily ordered) of selected attribute indexes
		/// </returns>
		/// <exception cref="Exception">if the search can't be completed
		/// </exception>
		public override int[] search(ASEvaluation ASEval, Instances data)
		{
			double best_merit;
			int sizeOfBest = m_numAttribs;
			System.Collections.BitArray temp;
			m_bestGroup = new System.Collections.BitArray((m_numAttribs % 64 == 0?m_numAttribs / 64:m_numAttribs / 64 + 1) * 64);
			
			m_onlyConsiderBetterAndSmaller = false;
			if (!(ASEval is SubsetEvaluator))
			{
				throw new System.Exception(ASEval.GetType().FullName + " is not a " + "Subset evaluator!");
			}
			
			//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.util.Random.Random'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
			m_random = new System.Random((System.Int32) m_seed);
			
			if (ASEval is UnsupervisedSubsetEvaluator)
			{
				m_hasClass = false;
			}
			else
			{
				m_hasClass = true;
				m_classIndex = data.classIndex();
			}
			
			SubsetEvaluator ASEvaluator = (SubsetEvaluator) ASEval;
			m_numAttribs = data.numAttributes();
			
			m_startRange.Upper=m_numAttribs - 1;
			if (!(StartSet.Equals("")))
			{
				m_starting = m_startRange.Selection;
			}
			
			// If a starting subset has been supplied, then initialise the bitset
			if (m_starting != null)
			{
				for (int i = 0; i < m_starting.Length; i++)
				{
					if ((m_starting[i]) != m_classIndex)
					{
						//SupportClass.BitArraySupport.Set(m_bestGroup, m_starting[i]);
                        m_bestGroup.Set(m_starting[i], true);
					}
				}
				m_onlyConsiderBetterAndSmaller = true;
				best_merit = ASEvaluator.evaluateSubset(m_bestGroup);
				sizeOfBest = countFeatures(m_bestGroup);
			}
			else
			{
				// do initial random subset
				m_bestGroup = generateRandomSubset();
				best_merit = ASEvaluator.evaluateSubset(m_bestGroup);
			}
			
			if (m_verbose)
			{
				System.Console.Out.WriteLine("Initial subset (" + Utils.doubleToString(System.Math.Abs(best_merit), 8, 5) + "): " + printSubset(m_bestGroup));
			}
			
			int i2;
			if (m_hasClass)
			{
				i2 = m_numAttribs - 1;
			}
			else
			{
				i2 = m_numAttribs;
			}
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			m_iterations = (int) ((m_searchSize * System.Math.Pow(2, i2)));
			
			int tempSize;
			double tempMerit;
			// main loop
			for (i2 = 0; i2 < m_iterations; i2++)
			{
				temp = generateRandomSubset();
				if (m_onlyConsiderBetterAndSmaller)
				{
					tempSize = countFeatures(temp);
					if (tempSize <= sizeOfBest)
					{
						tempMerit = ASEvaluator.evaluateSubset(temp);
						if (tempMerit >= best_merit)
						{
							sizeOfBest = tempSize;
							m_bestGroup = temp;
							best_merit = tempMerit;
							if (m_verbose)
							{
								System.Console.Out.Write("New best subset (" + Utils.doubleToString(System.Math.Abs(best_merit), 8, 5) + "): " + printSubset(m_bestGroup) + " :");
								System.Console.Out.WriteLine(Utils.doubleToString((((double) i2) / ((double) m_iterations) * 100.0), 5, 1) + "% done");
							}
						}
					}
				}
				else
				{
					tempMerit = ASEvaluator.evaluateSubset(temp);
					if (tempMerit > best_merit)
					{
						m_bestGroup = temp;
						best_merit = tempMerit;
						if (m_verbose)
						{
							System.Console.Out.Write("New best subset (" + Utils.doubleToString(System.Math.Abs(best_merit), 8, 5) + "): " + printSubset(m_bestGroup) + " :");
							System.Console.Out.WriteLine(Utils.doubleToString((((double) i2) / ((double) m_iterations) * 100.0), 5, 1) + "% done");
						}
					}
				}
			}
			m_bestMerit = best_merit;
			return attributeList(m_bestGroup);
		}
		
		/// <summary> prints a subset as a series of attribute numbers</summary>
		/// <param name="temp">the subset to print
		/// </param>
		/// <returns> a subset as a String of attribute numbers
		/// </returns>
		private System.String printSubset(System.Collections.BitArray temp)
		{
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			
			for (int j = 0; j < m_numAttribs; j++)
			{
				if (temp.Get(j))
				{
					text.Append((j + 1) + " ");
				}
			}
			return text.ToString();
		}
		
		/// <summary> converts a BitSet into a list of attribute indexes </summary>
		/// <param name="group">the BitSet to convert
		/// </param>
		/// <returns> an array of attribute indexes
		/// 
		/// </returns>
		private int[] attributeList(System.Collections.BitArray group)
		{
			int count = 0;
			
			// count how many were selected
			for (int i = 0; i < m_numAttribs; i++)
			{
				if (group.Get(i))
				{
					count++;
				}
			}
			
			int[] list = new int[count];
			count = 0;
			
			for (int i = 0; i < m_numAttribs; i++)
			{
				if (group.Get(i))
				{
					list[count++] = i;
				}
			}
			
			return list;
		}
		
		/// <summary> generates a random subset</summary>
		/// <returns> a random subset as a BitSet
		/// </returns>
		private System.Collections.BitArray generateRandomSubset()
		{
			System.Collections.BitArray temp = new System.Collections.BitArray((m_numAttribs % 64 == 0?m_numAttribs / 64:m_numAttribs / 64 + 1) * 64);
			double r;
			
			for (int i = 0; i < m_numAttribs; i++)
			{
				r = m_random.NextDouble();
				if (r <= 0.5)
				{
					if (m_hasClass && i == m_classIndex)
					{
					}
					else
					{
						//SupportClass.BitArraySupport.Set(temp, i);
                        temp.Set(i, true);
					}
				}
			}
			return temp;
		}
		
		/// <summary> counts the number of features in a subset</summary>
		/// <param name="featureSet">the feature set for which to count the features
		/// </param>
		/// <returns> the number of features in the subset
		/// </returns>
		private int countFeatures(System.Collections.BitArray featureSet)
		{
			int count = 0;
			for (int i = 0; i < m_numAttribs; i++)
			{
				if (featureSet.Get(i))
				{
					count++;
				}
			}
			return count;
		}
		
		/// <summary> resets to defaults</summary>
		private void  resetOptions()
		{
			m_starting = null;
			m_startRange = new Range();
			m_searchSize = 0.25;
			m_seed = 1;
			m_onlyConsiderBetterAndSmaller = false;
			m_verbose = false;
		}
	}
}