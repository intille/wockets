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
*    Ranker.java
*    Copyright (C) 1999 Mark Hall
*
*/
using System;
//UPGRADE_TODO: The package 'weka.core' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using weka.core;
namespace weka.attributeSelection
{
	
	/// <summary> Class for ranking the attributes evaluated by a AttributeEvaluator
	/// 
	/// Valid options are: <p>
	/// 
	/// -P <start set> <br>
	/// Specify a starting set of attributes. Eg 1,4,7-9. <p>
	/// 
	/// -T <threshold> <br>
	/// Specify a threshold by which the AttributeSelection module can. <br>
	/// discard attributes. <p>
	/// 
	/// </summary>
	/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.21 $
	/// </version>
	[Serializable]
	public class Ranker:ASSearch, RankedOutputSearch, StartSetHandler, OptionHandler
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the number of attributes to be retained.</summary>
		/// <returns> the number of attributes to retain
		/// </returns>
		/// <summary> Specify the number of attributes to select from the ranked list. -1
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
		/// <summary> Gets the calculated number to select. This might be computed
		/// from a threshold, or if < 0 is set as the number to select then
		/// it is set to the number of attributes in the (transformed) data.
		/// </summary>
		/// <returns> the calculated number of attributes to select
		/// </returns>
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
		/// <summary> This is a dummy method. Ranker can ONLY be used with attribute
		/// evaluators and as such can only produce a ranked list of attributes
		/// </summary>
		/// <returns> true all the time.
		/// </returns>
		/// <summary> This is a dummy set method---Ranker is ONLY capable of producing
		/// a ranked list of attributes for attribute evaluators.
		/// </summary>
		/// <param name="doRank">this parameter is N/A and is ignored
		/// </param>
		virtual public bool GenerateRanking
		{
			get
			{
				return true;
			}
			
			set
			{
				
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
		/// -P <start set> <br>
		/// Specify a starting set of attributes. Eg 1,4,7-9. <p>
		/// 
		/// -T <threshold> <br>
		/// Specify a threshold by which the AttributeSelection module can <br>
		/// discard attributes. <p>
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
				System.String[] options = new System.String[6];
				int current = 0;
				
				if (!(StartSet.Equals("")))
				{
					options[current++] = "-P";
					options[current++] = "" + startSetToString();
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
				
				optionString = Utils.getOption('P', value);
				if (optionString.Length != 0)
				{
					StartSet = optionString;
				}
				
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
		
		/// <summary>Holds the starting set as an array of attributes </summary>
		private int[] m_starting;
		
		/// <summary>Holds the start set for the search as a range </summary>
		private Range m_startRange;
		
		/// <summary>Holds the ordered list of attributes </summary>
		private int[] m_attributeList;
		
		/// <summary>Holds the list of attribute merit scores </summary>
		private double[] m_attributeMerit;
		
		/// <summary>Data has class attribute---if unsupervised evaluator then no class </summary>
		private bool m_hasClass;
		
		/// <summary>Class index of the data if supervised evaluator </summary>
		private int m_classIndex;
		
		/// <summary>The number of attribtes </summary>
		private int m_numAttribs;
		
		/// <summary> A threshold by which to discard attributes---used by the
		/// AttributeSelection module
		/// </summary>
		private double m_threshold;
		
		/// <summary>The number of attributes to select. -1 indicates that all attributes
		/// are to be retained. Has precedence over m_threshold 
		/// </summary>
		private int m_numToSelect = - 1;
		
		/// <summary>Used to compute the number to select </summary>
		private int m_calculatedNumToSelect = - 1;
		
		/// <summary> Returns a string describing this search method</summary>
		/// <returns> a description of the search suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String globalInfo()
		{
			return "Ranker : \n\nRanks attributes by their individual evaluations. " + "Use in conjunction with attribute evaluators (ReliefF, GainRatio, " + "Entropy etc).\n";
		}
		
		/// <summary> Constructor</summary>
		public Ranker()
		{
			resetOptions();
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
		public virtual System.String thresholdTipText()
		{
			return "Set threshold by which attributes can be discarded. Default value " + "results in no attributes being discarded. Use either this option or " + "numToSelect to reduce the attribute set.";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String generateRankingTipText()
		{
			return "A constant option. Ranker is only capable of generating " + " attribute rankings.";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String startSetTipText()
		{
			return "Specify a set of attributes to ignore. " + " When generating the ranking, Ranker will not evaluate the attributes " + " in this list. " + "This is specified as a comma " + "seperated list off attribute indexes starting at 1. It can include " + "ranges. Eg. 1,2,5-9,17.";
		}
		
		/// <summary> Returns an enumeration describing the available options.</summary>
		/// <returns> an enumeration of all the available options.
		/// 
		/// </returns>
		public virtual System.Collections.IEnumerator listOptions()
		{
			System.Collections.ArrayList newVector = System.Collections.ArrayList.Synchronized(new System.Collections.ArrayList(3));
			
			newVector.Add(new Option("\tSpecify a starting set of attributes." + "\n\tEg. 1,3,5-7." + "\t\nAny starting attributes specified are" + "\t\nignored during the ranking.", "P", 1, "-P <start set>"));
			newVector.Add(new Option("\tSpecify a theshold by which attributes" + "\tmay be discarded from the ranking.", "T", 1, "-T <threshold>"));
			
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
		
		/// <summary> Kind of a dummy search algorithm. Calls a Attribute evaluator to
		/// evaluate each attribute not included in the startSet and then sorts
		/// them to produce a ranked list of attributes.
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
			
			if (!(ASEval is AttributeEvaluator))
			{
				throw new System.Exception(ASEval.GetType().FullName + " is not a" + "Attribute evaluator!");
			}
			
			m_numAttribs = data.numAttributes();
			
			if (ASEval is UnsupervisedAttributeEvaluator)
			{
				m_hasClass = false;
			}
			else
			{
				m_classIndex = data.classIndex();
				if (m_classIndex >= 0)
				{
					m_hasClass = true;
				}
				else
				{
					m_hasClass = false;
				}
			}
			
			// get the transformed data and check to see if the transformer
			// preserves a class index
			if (ASEval is AttributeTransformer)
			{
				data = ((AttributeTransformer) ASEval).transformedHeader();
				if (m_classIndex >= 0 && data.classIndex() >= 0)
				{
					m_classIndex = data.classIndex();
					m_hasClass = true;
				}
			}
			
			
			m_startRange.Upper=m_numAttribs - 1;
			if (!(StartSet.Equals("")))
			{
				m_starting = m_startRange.Selection;
			}
			
			int sl = 0;
			if (m_starting != null)
			{
				sl = m_starting.Length;
			}
			if ((m_starting != null) && (m_hasClass == true))
			{
				// see if the supplied list contains the class index
				bool ok = false;
				for (i = 0; i < sl; i++)
				{
					if (m_starting[i] == m_classIndex)
					{
						ok = true;
						break;
					}
				}
				
				if (ok == false)
				{
					sl++;
				}
			}
			else
			{
				if (m_hasClass == true)
				{
					sl++;
				}
			}
			
			
			m_attributeList = new int[m_numAttribs - sl];
			m_attributeMerit = new double[m_numAttribs - sl];
			
			// add in those attributes not in the starting (omit list)
			for (i = 0, j = 0; i < m_numAttribs; i++)
			{
				if (!inStarting(i))
				{
					m_attributeList[j++] = i;
				}
			}
			
			AttributeEvaluator ASEvaluator = (AttributeEvaluator) ASEval;
			
			for (i = 0; i < m_attributeList.Length; i++)
			{
				m_attributeMerit[i] = ASEvaluator.evaluateAttribute(m_attributeList[i]);
			}
			
			double[][] tempRanked = rankedAttributes();
			int[] myrankedAttributes = new int[m_attributeList.Length];
			
			for (i = 0; i < m_attributeList.Length; i++)
			{
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				myrankedAttributes[i] = (int) tempRanked[i][0];
			}
			
			return myrankedAttributes;
		}
		
		
		/// <summary> Sorts the evaluated attribute list
		/// 
		/// </summary>
		/// <returns> an array of sorted (highest eval to lowest) attribute indexes
		/// </returns>
		/// <exception cref="Exception">of sorting can't be done.
		/// </exception>
		public virtual double[][] rankedAttributes()
		{
			int i, j;
			
			if (m_attributeList == null || m_attributeMerit == null)
			{
				throw new System.Exception("Search must be performed before a ranked " + "attribute list can be obtained");
			}
			
			int[] ranked = Utils.sort(m_attributeMerit);
			// reverse the order of the ranked indexes
			double[][] bestToWorst = new double[ranked.Length][];
			for (int i2 = 0; i2 < ranked.Length; i2++)
			{
				bestToWorst[i2] = new double[2];
			}
			
			for (i = ranked.Length - 1, j = 0; i >= 0; i--)
			{
				bestToWorst[j++][0] = ranked[i];
			}
			
			// convert the indexes to attribute indexes
			for (i = 0; i < bestToWorst.Length; i++)
			{
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				int temp = ((int) bestToWorst[i][0]);
				bestToWorst[i][0] = m_attributeList[temp];
				bestToWorst[i][1] = m_attributeMerit[temp];
			}
			
			if (m_numToSelect > bestToWorst.Length)
			{
				throw new System.Exception("More attributes requested than exist in the data");
			}
			
			if (m_numToSelect <= 0)
			{
				//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
				if (m_threshold == - System.Double.MaxValue)
				{
					m_calculatedNumToSelect = bestToWorst.Length;
				}
				else
				{
					determineNumToSelectFromThreshold(bestToWorst);
				}
			}
			/*    if (m_numToSelect > 0) {
			determineThreshFromNumToSelect(bestToWorst);
			} */
			
			return bestToWorst;
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
		
		private void  determineThreshFromNumToSelect(double[][] ranking)
		{
			if (m_numToSelect > ranking.Length)
			{
				throw new System.Exception("More attributes requested than exist in the data");
			}
			
			if (m_numToSelect == ranking.Length)
			{
				return ;
			}
			
			m_threshold = (ranking[m_numToSelect - 1][1] + ranking[m_numToSelect][1]) / 2.0;
		}
		
		/// <summary> returns a description of the search as a String</summary>
		/// <returns> a description of the search
		/// </returns>
		public override System.String ToString()
		{
			System.Text.StringBuilder BfString = new System.Text.StringBuilder();
			BfString.Append("\tAttribute ranking.\n");
			
			if (m_starting != null)
			{
				BfString.Append("\tIgnored attributes: ");
				
				BfString.Append(startSetToString());
				BfString.Append("\n");
			}
			
			//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
			if (m_threshold != - System.Double.MaxValue)
			{
				BfString.Append("\tThreshold for discarding attributes: " + Utils.doubleToString(m_threshold, 8, 4) + "\n");
			}
			
			return BfString.ToString();
		}
		
		
		/// <summary> Resets stuff to default values</summary>
		protected internal virtual void  resetOptions()
		{
			m_starting = null;
			m_startRange = new Range();
			m_attributeList = null;
			m_attributeMerit = null;
			//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
			m_threshold = - System.Double.MaxValue;
		}
		
		
		private bool inStarting(int feat)
		{
			// omit the class from the evaluation
			if ((m_hasClass == true) && (feat == m_classIndex))
			{
				return true;
			}
			
			if (m_starting == null)
			{
				return false;
			}
			
			for (int i = 0; i < m_starting.Length; i++)
			{
				if (m_starting[i] == feat)
				{
					return true;
				}
			}
			
			return false;
		}
	}
}