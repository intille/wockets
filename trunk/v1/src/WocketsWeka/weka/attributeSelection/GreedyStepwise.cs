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
*    GreedyStepwise.java
*    Copyright (C) 2004 Mark Hall
*
*/
using System;
//UPGRADE_TODO: The package 'weka.core' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using weka.core;
namespace weka.attributeSelection
{
	
	/// <summary> Class for performing a hill climbing search (either forwards or backwards). <p>
	/// 
	/// Valid options are: <p>
	/// -B <br>
	/// Use a backward search instead of a forward one. <p>
	/// 
	/// -P <start set> <br>
	/// Specify a starting set of attributes. Eg 1,4,7-9. <p>
	/// 
	/// -R <br>
	/// Produce a ranked list of attributes. <p>
	/// 
	/// -T <threshold> <br>
	/// Specify a threshold by which the AttributeSelection module can. <br>
	/// discard attributes. Use in conjunction with -R <p>
	/// 
	/// </summary>
	/// <author>  Mark Hall
	/// </author>
	/// <version>  $Revision: 1.4 $
	/// </version>
	[Serializable]
	public class GreedyStepwise:ASSearch, RankedOutputSearch, StartSetHandler, OptionHandler
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Get whether to search backwards
		/// 
		/// </summary>
		/// <returns> true if the search will proceed backwards
		/// </returns>
		/// <summary> Set whether to search backwards instead of forwards
		/// 
		/// </summary>
		/// <param name="back">true to search backwards
		/// </param>
		virtual public bool SearchBackwards
		{
			get
			{
				return m_backward;
			}
			
			set
			{
				m_backward = value;
				if (m_backward)
				{
					GenerateRanking = false;
				}
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Returns the threshold so that the AttributeSelection module can
		/// discard attributes from the ranking.
		/// </summary>
		/// <summary> Set the threshold by which the AttributeSelection module can discard
		/// attributes.
		/// </summary>
		/// <param name="threshold">the threshold.
		/// </param>
		virtual public double Threshold
		{
			get
			{
				return m_threshold;
			}
			
			set
			{
				m_threshold = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the number of attributes to be retained.</summary>
		/// <returns> the number of attributes to retain
		/// </returns>
		/// <summary> Specify the number of attributes to select from the ranked list
		/// (if generating a ranking). -1
		/// indicates that all attributes are to be retained.
		/// </summary>
		/// <param name="n">the number of attributes to retain
		/// </param>
		virtual public int NumToSelect
		{
			get
			{
				return m_numToSelect;
			}
			
			set
			{
				m_numToSelect = value;
			}
			
		}
		/// <summary> Gets the calculated number of attributes to retain. This is the
		/// actual number of attributes to retain. This is the same as
		/// getNumToSelect if the user specifies a number which is not less
		/// than zero. Otherwise it should be the number of attributes in the
		/// (potentially transformed) data.
		/// </summary>
		virtual public int CalculatedNumToSelect
		{
			get
			{
				if (m_numToSelect >= 0)
				{
					m_calculatedNumToSelect = m_numToSelect;
				}
				return m_calculatedNumToSelect;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets whether ranking has been requested. This is used by the
		/// AttributeSelection module to determine if rankedAttributes()
		/// should be called.
		/// </summary>
		/// <returns> true if ranking has been requested.
		/// </returns>
		/// <summary> Records whether the user has requested a ranked list of attributes.</summary>
		/// <param name="doRank">true if ranking is requested
		/// </param>
		virtual public bool GenerateRanking
		{
			get
			{
				return m_rankingRequested;
			}
			
			set
			{
				m_rankingRequested = value;
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
		/// eg. 1,2,6,10-15.
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
		/// <summary> Gets the current settings of ReliefFAttributeEval.
		/// 
		/// </summary>
		/// <returns> an array of strings suitable for passing to setOptions()
		/// </returns>
		/// <summary> Parses a given list of options.
		/// 
		/// Valid options are: <p>
		/// 
		/// -B <br>
		/// Use a backward search instead of a forward one. <p>
		/// 
		/// -P <start set> <br>
		/// Specify a starting set of attributes. Eg 1,4,7-9. <p>
		/// 
		/// -R <br>
		/// Produce a ranked list of attributes. <p>
		/// 
		/// -T <threshold> <br>
		/// Specify a threshold by which the AttributeSelection module can <br>
		/// discard attributes. Use in conjunction with -R <p>
		/// 
		/// -N <number to retain> <br>
		/// Specify the number of attributes to retain. Overides any threshold. <br>
		/// <p>
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
				System.String[] options = new System.String[8];
				int current = 0;
				
				if (SearchBackwards)
				{
					options[current++] = "-B";
				}
				
				if (!(StartSet.Equals("")))
				{
					options[current++] = "-P";
					options[current++] = "" + startSetToString();
				}
				
				if (GenerateRanking)
				{
					options[current++] = "-R";
				}
				options[current++] = "-T";
				options[current++] = "" + Threshold;
				
				options[current++] = "-N";
				options[current++] = "" + NumToSelect;
				
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
				
				SearchBackwards = Utils.getFlag('B', value);
				
				optionString = Utils.getOption('P', value);
				if (optionString.Length != 0)
				{
					StartSet = optionString;
				}
				
				GenerateRanking = Utils.getFlag('R', value);
				
				optionString = Utils.getOption('T', value);
				if (optionString.Length != 0)
				{
					System.Double temp;
					temp = System.Double.Parse(optionString);
					Threshold = temp;
				}
				
				optionString = Utils.getOption('N', value);
				if (optionString.Length != 0)
				{
					NumToSelect = System.Int32.Parse(optionString);
				}
			}
			
		}
		
		/// <summary>does the data have a class </summary>
		protected internal bool m_hasClass;
		
		/// <summary>holds the class index </summary>
		protected internal int m_classIndex;
		
		/// <summary>number of attributes in the data </summary>
		protected internal int m_numAttribs;
		
		/// <summary>true if the user has requested a ranked list of attributes </summary>
		protected internal bool m_rankingRequested;
		
		/// <summary> go from one side of the search space to the other in order to generate
		/// a ranking
		/// </summary>
		protected internal bool m_doRank;
		
		/// <summary>used to indicate whether or not ranking has been performed </summary>
		protected internal bool m_doneRanking;
		
		/// <summary> A threshold by which to discard attributes---used by the
		/// AttributeSelection module
		/// </summary>
		protected internal double m_threshold;
		
		/// <summary>The number of attributes to select. -1 indicates that all attributes
		/// are to be retained. Has precedence over m_threshold 
		/// </summary>
		protected internal int m_numToSelect = - 1;
		
		protected internal int m_calculatedNumToSelect;
		
		/// <summary>the merit of the best subset found </summary>
		protected internal double m_bestMerit;
		
		/// <summary>a ranked list of attribute indexes </summary>
		protected internal double[][] m_rankedAtts;
		protected internal int m_rankedSoFar;
		
		/// <summary>the best subset found </summary>
		protected internal System.Collections.BitArray m_best_group;
		protected internal ASEvaluation m_ASEval;
		
		protected internal Instances m_Instances;
		
		/// <summary>holds the start set for the search as a Range </summary>
		protected internal Range m_startRange;
		
		/// <summary>holds an array of starting attributes </summary>
		protected internal int[] m_starting;
		
		/// <summary>Use a backwards search instead of a forwards one </summary>
		protected internal bool m_backward = false;
		
		/// <summary> Returns a string describing this search method</summary>
		/// <returns> a description of the search suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String globalInfo()
		{
			return "GreedyStepwise :\n\nPerforms a greedy forward or backward search " + "through " + "the space of attribute subsets. May start with no/all attributes or from " + "an arbitrary point in the space. Stops when the addition/deletion of any " + "remaining attributes results in a decrease in evaluation. " + "Can also produce a ranked list of " + "attributes by traversing the space from one side to the other and " + "recording the order that attributes are selected.\n";
		}
		
		public GreedyStepwise()
		{
			//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
			m_threshold = - System.Double.MaxValue;
			m_doneRanking = false;
			m_startRange = new Range();
			m_starting = null;
			resetOptions();
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String searchBackwardsTipText()
		{
			return "Search backwards rather than forwards.";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String thresholdTipText()
		{
			return "Set threshold by which attributes can be discarded. Default value " + "results in no attributes being discarded. Use in conjunction with " + "generateRanking";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String numToSelectTipText()
		{
			return "Specify the number of attributes to retain. The default value " + "(-1) indicates that all attributes are to be retained. Use either " + "this option or a threshold to reduce the attribute set.";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String generateRankingTipText()
		{
			return "Set to true if a ranked list is required.";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String startSetTipText()
		{
			return "Set the start point for the search. This is specified as a comma " + "seperated list off attribute indexes starting at 1. It can include " + "ranges. Eg. 1,2,5-9,17.";
		}
		
		/// <summary> Returns an enumeration describing the available options.</summary>
		/// <returns> an enumeration of all the available options.
		/// 
		/// </returns>
		public virtual System.Collections.IEnumerator listOptions()
		{
			System.Collections.ArrayList newVector = System.Collections.ArrayList.Synchronized(new System.Collections.ArrayList(4));
			
			newVector.Add(new Option("\tUse a backward search instead  of a" + "\n\tforward one.", "-B", 0, "-B"));
			newVector.Add(new Option("\tSpecify a starting set of attributes." + "\n\tEg. 1,3,5-7.", "P", 1, "-P <start set>"));
			
			newVector.Add(new Option("\tProduce a ranked list of attributes.", "R", 0, "-R"));
			newVector.Add(new Option("\tSpecify a theshold by which attributes" + "\n\tmay be discarded from the ranking." + "\n\tUse in conjuction with -R", "T", 1, "-T <threshold>"));
			
			newVector.Add(new Option("\tSpecify number of attributes to select", "N", 1, "-N <num to select>"));
			
			return newVector.GetEnumerator();
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
		protected internal virtual System.String startSetToString()
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
		
		/// <summary> returns a description of the search.</summary>
		/// <returns> a description of the search as a String.
		/// </returns>
		public override System.String ToString()
		{
			System.Text.StringBuilder FString = new System.Text.StringBuilder();
			FString.Append("\tGreedy Stepwise (" + ((m_backward)?"backwards)":"forwards)") + ".\n\tStart set: ");
			
			if (m_starting == null)
			{
				if (m_backward)
				{
					FString.Append("all attributes\n");
				}
				else
				{
					FString.Append("no attributes\n");
				}
			}
			else
			{
				FString.Append(startSetToString() + "\n");
			}
			if (!m_doneRanking)
			{
				FString.Append("\tMerit of best subset found: " + Utils.doubleToString(System.Math.Abs(m_bestMerit), 8, 3) + "\n");
			}
			
			//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
			if ((m_threshold != - System.Double.MaxValue) && (m_doneRanking))
			{
				FString.Append("\tThreshold for discarding attributes: " + Utils.doubleToString(m_threshold, 8, 4) + "\n");
			}
			
			return FString.ToString();
		}
		
		
		/// <summary> Searches the attribute subset space by forward selection.
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
			
			int i, j;
			//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
			double best_merit = - System.Double.MaxValue;
			double temp_best, temp_merit;
			int temp_index = 0;
			System.Collections.BitArray temp_group;
			
			if (data != null)
			{
				// this is a fresh run so reset
				resetOptions();
				m_Instances = data;
			}
			m_ASEval = ASEval;
			
			m_numAttribs = m_Instances.numAttributes();
			
			if (m_best_group == null)
			{
				m_best_group = new System.Collections.BitArray((m_numAttribs % 64 == 0?m_numAttribs / 64:m_numAttribs / 64 + 1) * 64);
			}
			
			if (!(m_ASEval is SubsetEvaluator))
			{
				throw new System.Exception(m_ASEval.GetType().FullName + " is not a " + "Subset evaluator!");
			}
			
			m_startRange.Upper=m_numAttribs - 1;
			if (!(StartSet.Equals("")))
			{
                m_starting = m_startRange.Selection;
			}
			
			if (m_ASEval is UnsupervisedSubsetEvaluator)
			{
				m_hasClass = false;
				m_classIndex = - 1;
			}
			else
			{
				m_hasClass = true;
				m_classIndex = m_Instances.classIndex();
			}
			
			SubsetEvaluator ASEvaluator = (SubsetEvaluator) m_ASEval;
			
			if (m_rankedAtts == null)
			{
				double[][] tmpArray = new double[m_numAttribs][];
				for (int i2 = 0; i2 < m_numAttribs; i2++)
				{
					tmpArray[i2] = new double[2];
				}
				m_rankedAtts = tmpArray;
				m_rankedSoFar = 0;
			}
			
			// If a starting subset has been supplied, then initialise the bitset
			if (m_starting != null)
			{
				for (i = 0; i < m_starting.Length; i++)
				{
					if ((m_starting[i]) != m_classIndex)
					{
						//SupportClass.BitArraySupport.Set(m_best_group, m_starting[i]);
                        m_best_group.Set(m_starting[i], true);
					}
				}
			}
			else
			{
				if (m_backward)
				{
					for (i = 0, j = 0; i < m_numAttribs; i++)
					{
						if (i != m_classIndex)
						{
							//SupportClass.BitArraySupport.Set(m_best_group, i);
                            m_best_group.Set(i, true);
						}
					}
				}
			}
			
			// Evaluate the initial subset
			best_merit = ASEvaluator.evaluateSubset(m_best_group);
			
			// main search loop
			bool done = false;
			bool addone = false;
			bool z;
			while (!done)
			{
				temp_group = (System.Collections.BitArray) m_best_group.Clone();
				temp_best = best_merit;
				if (m_doRank)
				{
					//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
					temp_best = - System.Double.MaxValue;
				}
				done = true;
				addone = false;
				for (i = 0; i < m_numAttribs; i++)
				{
					if (m_backward)
					{
						z = ((i != m_classIndex) && (temp_group.Get(i)));
					}
					else
					{
						z = ((i != m_classIndex) && (!temp_group.Get(i)));
					}
					if (z)
					{
						// set/unset the bit
						if (m_backward)
						{
							temp_group.Set(i, false);
						}
						else
						{
							//SupportClass.BitArraySupport.Set(temp_group, i);
                            temp_group.Set(i, true);
						}
						temp_merit = ASEvaluator.evaluateSubset(temp_group);
						if (m_backward)
						{
							z = (temp_merit >= temp_best);
						}
						else
						{
							z = (temp_merit > temp_best);
						}
						if (z)
						{
							temp_best = temp_merit;
							temp_index = i;
							addone = true;
							done = false;
						}
						
						// unset this addition/deletion
						if (m_backward)
						{
							//SupportClass.BitArraySupport.Set(temp_group, i);
                            temp_group.Set(i, true);
						}
						else
						{
							temp_group.Set(i, false);
						}
						if (m_doRank)
						{
							done = false;
						}
					}
				}
				if (addone)
				{
					if (m_backward)
					{
						m_best_group.Set(temp_index, false);
					}
					else
					{
						//SupportClass.BitArraySupport.Set(m_best_group, temp_index);
                        m_best_group.Set(temp_index, true);
					}
					best_merit = temp_best;
					m_rankedAtts[m_rankedSoFar][0] = temp_index;
					m_rankedAtts[m_rankedSoFar][1] = best_merit;
					m_rankedSoFar++;
				}
			}
			m_bestMerit = best_merit;
			return attributeList(m_best_group);
		}
		
		/// <summary> Produces a ranked list of attributes. Search must have been performed
		/// prior to calling this function. Search is called by this function to
		/// complete the traversal of the the search space. A list of
		/// attributes and merits are returned. The attributes a ranked by the
		/// order they are added to the subset during a forward selection search.
		/// Individual merit values reflect the merit associated with adding the
		/// corresponding attribute to the subset; because of this, merit values
		/// may initially increase but then decrease as the best subset is
		/// "passed by" on the way to the far side of the search space.
		/// 
		/// </summary>
		/// <returns> an array of attribute indexes and associated merit values
		/// </returns>
		/// <exception cref="Exception">if something goes wrong.
		/// </exception>
		public virtual double[][] rankedAttributes()
		{
			
			if (m_rankedAtts == null || m_rankedSoFar == - 1)
			{
				throw new System.Exception("Search must be performed before attributes " + "can be ranked.");
			}
			m_doRank = true;
			search(m_ASEval, null);
			
			double[][] final_rank = new double[m_rankedSoFar][];
			for (int i = 0; i < m_rankedSoFar; i++)
			{
				final_rank[i] = new double[2];
			}
			for (int i = 0; i < m_rankedSoFar; i++)
			{
				final_rank[i][0] = m_rankedAtts[i][0];
				final_rank[i][1] = m_rankedAtts[i][1];
			}
			
			resetOptions();
			m_doneRanking = true;
			
			if (m_numToSelect > final_rank.Length)
			{
				throw new System.Exception("More attributes requested than exist in the data");
			}
			
			if (m_numToSelect <= 0)
			{
				//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
				if (m_threshold == - System.Double.MaxValue)
				{
					m_calculatedNumToSelect = final_rank.Length;
				}
				else
				{
					determineNumToSelectFromThreshold(final_rank);
				}
			}
			
			return final_rank;
		}
		
		private void  determineNumToSelectFromThreshold(double[][] ranking)
		{
			int count = 0;
			for (int i = 0; i < ranking.Length; i++)
			{
				if (ranking[i][1] > m_threshold)
				{
					count++;
				}
			}
			m_calculatedNumToSelect = count;
		}
		
		/// <summary> converts a BitSet into a list of attribute indexes </summary>
		/// <param name="group">the BitSet to convert
		/// </param>
		/// <returns> an array of attribute indexes
		/// 
		/// </returns>
		protected internal virtual int[] attributeList(System.Collections.BitArray group)
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
		
		/// <summary> Resets options</summary>
		protected internal virtual void  resetOptions()
		{
			m_doRank = false;
			m_best_group = null;
			m_ASEval = null;
			m_Instances = null;
			m_rankedSoFar = - 1;
			m_rankedAtts = null;
		}
	}
}