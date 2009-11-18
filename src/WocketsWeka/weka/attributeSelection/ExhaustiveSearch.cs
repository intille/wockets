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
*    ExhaustiveSearch.java
*    Copyright (C) 1999 Mark Hall
*
*/
using System;
//UPGRADE_TODO: The package 'weka.core' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using weka.core;
namespace weka.attributeSelection
{
	
	
	/// <summary> Class for performing an exhaustive search. <p>
	/// 
	/// Valid options are: <p>
	/// 
	/// -V <br>
	/// Verbose output. Output new best subsets as the search progresses. <p>
	/// 
	/// </summary>
	/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.8.2.2 $
	/// </version>
	[Serializable]
	public class ExhaustiveSearch:ASSearch, OptionHandler
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the current settings of RandomSearch.</summary>
		/// <returns> an array of strings suitable for passing to setOptions()
		/// </returns>
		/// <summary> Parses a given list of options.
		/// 
		/// Valid options are: <p>
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
				System.String[] options = new System.String[1];
				int current = 0;
				
				if (m_verbose)
				{
					options[current++] = "-V";
				}
				
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
				
				Verbose = Utils.getFlag('V', value);
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
		
		/// <summary>the best feature set found during the search </summary>
		private System.Collections.BitArray m_bestGroup;
		
		/// <summary>the merit of the best subset found </summary>
		private double m_bestMerit;
		
		/// <summary>does the data have a class </summary>
		private bool m_hasClass;
		
		/// <summary>holds the class index </summary>
		private int m_classIndex;
		
		/// <summary>number of attributes in the data </summary>
		private int m_numAttribs;
		
		/// <summary>if true, then ouput new best subsets as the search progresses </summary>
		private bool m_verbose;
		
		/// <summary>the number of subsets evaluated during the search </summary>
		private int m_evaluations;
		
		/// <summary> Returns a string describing this search method</summary>
		/// <returns> a description of the search suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String globalInfo()
		{
			return "ExhaustiveSearch : \n\nPerforms an exhaustive search through " + "the space of attribute subsets starting from the empty set of " + "attrubutes. Reports the best subset found.";
		}
		
		/// <summary> Constructor</summary>
		public ExhaustiveSearch()
		{
			resetOptions();
		}
		
		/// <summary> Returns an enumeration describing the available options.</summary>
		/// <returns> an enumeration of all the available options.
		/// 
		/// </returns>
		public virtual System.Collections.IEnumerator listOptions()
		{
			System.Collections.ArrayList newVector = System.Collections.ArrayList.Synchronized(new System.Collections.ArrayList(2));
			
			newVector.Add(new Option("\tOutput subsets as the search progresses." + "\n\t(default = false).", "V", 0, "-V"));
			return newVector.GetEnumerator();
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String verboseTipText()
		{
			return "Print progress information. Sends progress info to the terminal " + "as the search progresses.";
		}
		
		/// <summary> prints a description of the search</summary>
		/// <returns> a description of the search as a string
		/// </returns>
		public override System.String ToString()
		{
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			
			text.Append("\tExhaustive Search.\n\tStart set: ");
			
			text.Append("no attributes\n");
			
			text.Append("\tNumber of evaluations: " + m_evaluations + "\n");
			text.Append("\tMerit of best subset found: " + Utils.doubleToString(System.Math.Abs(m_bestMerit), 8, 3) + "\n");
			
			return text.ToString();
		}
		
		/// <summary> Searches the attribute subset space using an exhaustive search.
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
			double tempMerit;
			int setSize;
			bool done = false;
			int sizeOfBest;
			int tempSize;
			
			////BigInteger space = BigInteger.ZERO;
			//UPGRADE_TODO: Class 'java.math.BigInteger' was converted to 'System.Decimal' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javamathBigInteger'"
			System.Int64 space = 0;
			
			m_numAttribs = data.numAttributes();
			m_bestGroup = new System.Collections.BitArray((m_numAttribs % 64 == 0?m_numAttribs / 64:m_numAttribs / 64 + 1) * 64);
			
			if (!(ASEval is SubsetEvaluator))
			{
				throw new System.Exception(ASEval.GetType().FullName + " is not a " + "Subset evaluator!");
			}
			
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
			
			best_merit = ASEvaluator.evaluateSubset(m_bestGroup);
			m_evaluations++;
			sizeOfBest = countFeatures(m_bestGroup);
			
			System.Collections.BitArray tempGroup = new System.Collections.BitArray((m_numAttribs % 64 == 0?m_numAttribs / 64:m_numAttribs / 64 + 1) * 64);
			tempMerit = ASEvaluator.evaluateSubset(tempGroup);
			
			if (m_verbose)
			{
				System.Console.Out.WriteLine("Zero feature subset (" + Utils.doubleToString(System.Math.Abs(tempMerit), 8, 5) + ")");
			}
			
			if (tempMerit >= best_merit)
			{
				tempSize = countFeatures(tempGroup);
				if (tempMerit > best_merit || (tempSize < sizeOfBest))
				{
					best_merit = tempMerit;
					m_bestGroup = (System.Collections.BitArray) (tempGroup.Clone());
					sizeOfBest = tempSize;
				}
			}
			
			int numatts = (m_hasClass)?m_numAttribs - 1:m_numAttribs;
			
			//UPGRADE_TODO: Class 'java.math.BigInteger' was converted to 'System.Decimal' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javamathBigInteger'"
			System.Decimal auxBigI = new System.Decimal(2);
			//UPGRADE_TODO: The equivalent in .NET for method 'java.math.BigInteger.pow' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
			auxBigI = System.Decimal.Subtract(System.Convert.ToDecimal(System.Math.Pow(System.Convert.ToDouble(auxBigI), System.Convert.ToDouble(numatts))), new System.Decimal(1));
			
			//UPGRADE_TODO: Class 'java.math.BigInteger' was converted to 'System.Decimal' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javamathBigInteger'"
			System.Decimal searchSpaceEnd = auxBigI;
			
			
			////BigInteger searchSpaceEnd = 
			////  BigInteger.ONE.add(BigInteger.ONE).pow(numatts).subtract(BigInteger.ONE);
			
			while (!done)
			{
				// the next subset
				////space = space.add(BigInteger.ONE);
                space++;// = System.Decimal.Add(space, new System.Decimal(1));
				if (space.Equals(searchSpaceEnd))
				{
					done = true;
				}
				
				////tempGroup.clear();
				//UPGRADE_TODO: Method 'java.util.BitSet.length' was converted to 'System.Collections.BitArray.Length' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilBitSetlength'"
				int n = tempGroup.Length;
				for (int i = 0; i < n; i++)
				{
					tempGroup.Set(i, false);
				}
				///////////////////////////////
				
				for (int i = 0; i < numatts; i++)
				{
					//UPGRADE_ISSUE: Method 'java.math.BigInteger.testBit' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javamathBigIntegertestBit_int'"
					if ( ((space & (1<<i)) !=0) && ((space & ~(1<<i)) == 0)) 
                        //instead of if (space.TestBit(i))
					{
						if (!m_hasClass)
						{
							//SupportClass.BitArraySupport.Set(tempGroup, i);
                            tempGroup.Set(i, true);
						}
						else
						{
							int j = (i >= m_classIndex)?i + 1:i;
							//SupportClass.BitArraySupport.Set(tempGroup, j);
                            tempGroup.Set(i, true);
						}
					}
				}
				
				tempMerit = ASEvaluator.evaluateSubset(tempGroup);
				m_evaluations++;
				if (tempMerit >= best_merit)
				{
					tempSize = countFeatures(tempGroup);
					if (tempMerit > best_merit || (tempSize < sizeOfBest))
					{
						best_merit = tempMerit;
						m_bestGroup = (System.Collections.BitArray) (tempGroup.Clone());
						sizeOfBest = tempSize;
						if (m_verbose)
						{
							System.Console.Out.WriteLine("New best subset (" + Utils.doubleToString(System.Math.Abs(best_merit), 8, 5) + "): " + printSubset(m_bestGroup));
						}
					}
				}
			}
			
			m_bestMerit = best_merit;
			
			return attributeList(m_bestGroup);
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
		
		/// <summary> generates the next subset of size "size" given the subset "temp".</summary>
		/// <param name="size">the size of the feature subset (eg. 2 means that the 
		/// current subset contains two features and the next generated subset
		/// should also contain 2 features).
		/// </param>
		/// <param name="temp">will hold the generated subset as a BitSet
		/// </param>
		private void  generateNextSubset(int size, System.Collections.BitArray temp)
		{
			int i, j;
			int counter = 0;
			bool done = false;
			System.Collections.BitArray temp2 = (System.Collections.BitArray) temp.Clone();
			
			System.Console.Error.WriteLine("Size: " + size);
			for (i = 0; i < m_numAttribs; i++)
			{
				temp2.Set(i, false);
			}
			
			while ((!done) && (counter < size))
			{
				for (i = m_numAttribs - 1 - counter; i >= 0; i--)
				{
					if (temp.Get(i))
					{
						
						temp.Set(i, false);
						
						int newP;
						if (i != (m_numAttribs - 1 - counter))
						{
							newP = i + 1;
							if (newP == m_classIndex)
							{
								newP++;
							}
							
							if (newP < m_numAttribs)
							{
								//SupportClass.BitArraySupport.Set(temp, newP);
                                temp.Set(newP, true);
								
								for (j = 0; j < counter; j++)
								{
									if (newP + 1 + j == m_classIndex)
									{
										newP++;
									}
									
									if (newP + 1 + j < m_numAttribs)
									{
										//SupportClass.BitArraySupport.Set(temp, newP + 1 + j);
                                        temp.Set(newP + 1 + j, true);
									}
								}
								done = true;
							}
							else
							{
								counter++;
							}
							break;
						}
						else
						{
							counter++;
							break;
						}
					}
				}
			}
			
			/////////////////////////////////////////////////
			
			////if (temp.cardinality() < size)
			////{
			////    temp.clear();
			////}
			
			int cardinality = 0;
			//UPGRADE_TODO: Method 'java.util.BitSet.length' was converted to 'System.Collections.BitArray.Length' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilBitSetlength'"
			int n = temp.Length;
			for (i = 0; i < n; i++)
			{
				if (temp.Get(i))
				{
					cardinality++;
				}
			}
			
			if (cardinality < size)
			{
				for (i = 0; i < n; i++)
				{
					temp.Set(i, false);
				}
			}
			
			/////////////////////////////////////////////////
			
			System.Console.Error.WriteLine(printSubset(temp).ToString());
		}
		
		/// <summary> resets to defaults</summary>
		private void  resetOptions()
		{
			m_verbose = false;
			m_evaluations = 0;
		}
	}
}