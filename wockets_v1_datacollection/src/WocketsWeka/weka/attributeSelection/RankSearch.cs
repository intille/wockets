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
*    RankSearch.java
*    Copyright (C) 1999 Mark Hall
*
*/
using System;
//UPGRADE_TODO: The package 'weka.core' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using weka.core;
namespace weka.attributeSelection
{
	
	/// <summary> Class for evaluating a attribute ranking (given by a specified
	/// evaluator) using a specified subset evaluator. <p>
	/// 
	/// Valid options are: <p>
	/// 
	/// -A <attribute/subset evaluator> <br>
	/// Specify the attribute/subset evaluator to be used for generating the 
	/// ranking. If a subset evaluator is specified then a forward selection
	/// search is used to produce a ranked list of attributes.<p>
	/// 
	/// </summary>
	/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.11 $
	/// </version>
	[Serializable]
	public class RankSearch:ASSearch, OptionHandler
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Get the attribute evaluator used to generate the ranking.</summary>
		/// <returns> the evaluator used to generate the ranking.
		/// </returns>
		/// <summary> Set the attribute evaluator to use for generating the ranking.</summary>
		/// <param name="newEvaluator">the attribute evaluator to use.
		/// </param>
		virtual public ASEvaluation AttributeEvaluator
		{
			get
			{
				return m_ASEval;
			}
			
			set
			{
				m_ASEval = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the current settings of WrapperSubsetEval.
		/// 
		/// </summary>
		/// <returns> an array of strings suitable for passing to setOptions()
		/// </returns>
		/// <summary> Parses a given list of options.
		/// 
		/// Valid options are:<p>
		/// 
		/// -A <attribute evaluator> <br>
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
				System.String[] evaluatorOptions = new System.String[0];
				
				if ((m_ASEval != null) && (m_ASEval is OptionHandler))
				{
					evaluatorOptions = ((OptionHandler) m_ASEval).Options;
				}
				
				System.String[] options = new System.String[4 + evaluatorOptions.Length];
				int current = 0;
				
				if (AttributeEvaluator != null)
				{
					options[current++] = "-A";
					options[current++] = AttributeEvaluator.GetType().FullName;
				}
				
				options[current++] = "--";
				Array.Copy(evaluatorOptions, 0, options, current, evaluatorOptions.Length);
				current += evaluatorOptions.Length;
				
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
				optionString = Utils.getOption('A', value);
				
				if (optionString.Length == 0)
				{
					throw new System.Exception("An attribute evaluator  must be specified with" + "-A option");
				}
				
				AttributeEvaluator = ASEvaluation.forName(optionString, Utils.partitionOptions(value));
			}
			
		}
		
		/// <summary>does the data have a class </summary>
		private bool m_hasClass;
		
		/// <summary>holds the class index </summary>
		private int m_classIndex;
		
		/// <summary>number of attributes in the data </summary>
		private int m_numAttribs;
		
		/// <summary>the best subset found </summary>
		private System.Collections.BitArray m_best_group;
		
		/// <summary>the attribute evaluator to use for generating the ranking </summary>
		private ASEvaluation m_ASEval;
		
		/// <summary>the subset evaluator with which to evaluate the ranking </summary>
		private ASEvaluation m_SubsetEval;
		
		/// <summary>the training instances </summary>
		private Instances m_Instances;
		
		/// <summary>the merit of the best subset found </summary>
		private double m_bestMerit;
		
		/// <summary>will hold the attribute ranking </summary>
		private int[] m_Ranking;
		
		/// <summary> Returns a string describing this search method</summary>
		/// <returns> a description of the search method suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String globalInfo()
		{
			return "RankSearch : \n\n" + "Uses an attribute/subset evaluator to rank all attributes. " + "If a subset evaluator is specified, then a forward selection " + "search is used to generate a ranked list. From the ranked " + "list of attributes, subsets of increasing size are evaluated, ie. " + "The best attribute, the best attribute plus the next best attribute, " + "etc.... The best attribute set is reported. RankSearch is linear in " + "the number of attributes if a simple attribute evaluator is used " + "such as GainRatioAttributeEval.\n";
		}
		
		public RankSearch()
		{
			resetOptions();
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String attributeEvaluatorTipText()
		{
			return "Attribute evaluator to use for generating a ranking.";
		}
		
		/// <summary> Returns an enumeration describing the available options.</summary>
		/// <returns> an enumeration of all the available options.
		/// 
		/// </returns>
		public virtual System.Collections.IEnumerator listOptions()
		{
			System.Collections.ArrayList newVector = System.Collections.ArrayList.Synchronized(new System.Collections.ArrayList(4));
			newVector.Add(new Option("\tclass name of attribute evaluator to" + "\n\tuse for ranking. Place any" + "\n\tevaluator options LAST on the" + "\n\tcommand line following a \"--\"." + "\n\teg. -A weka.attributeSelection." + "GainRatioAttributeEval ... " + "-- -M", "A", 1, "-A <attribute evaluator>"));
			
			if ((m_ASEval != null) && (m_ASEval is OptionHandler))
			{
				newVector.Add(new Option("", "", 0, "\nOptions specific to" + "evaluator " + m_ASEval.GetType().FullName + ":"));
				System.Collections.IEnumerator enu = ((OptionHandler) m_ASEval).listOptions();
				
				//UPGRADE_TODO: Method 'java.util.Enumeration.hasMoreElements' was converted to 'System.Collections.IEnumerator.MoveNext' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationhasMoreElements'"
				while (enu.MoveNext())
				{
					//UPGRADE_TODO: Method 'java.util.Enumeration.nextElement' was converted to 'System.Collections.IEnumerator.Current' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationnextElement'"
					newVector.Add(enu.Current);
				}
			}
			
			return newVector.GetEnumerator();
		}
		
		/// <summary> Reset the search method.</summary>
		protected internal virtual void  resetOptions()
		{
			m_ASEval = new GainRatioAttributeEval();
			m_Ranking = null;
		}
		
		/// <summary> Ranks attributes using the specified attribute evaluator and then
		/// searches the ranking using the supplied subset evaluator.
		/// 
		/// </summary>
		/// <param name="ASEvaluator">the subset evaluator to guide the search
		/// </param>
		/// <param name="data">the training instances.
		/// </param>
		/// <returns> an array (not necessarily ordered) of selected attribute indexes
		/// </returns>
		/// <exception cref="Exception">if the search can't be completed
		/// </exception>
		public override int[] search(ASEvaluation ASEval, Instances data)
		{
			
			//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
			double best_merit = - System.Double.MaxValue;
			double temp_merit;
			System.Collections.BitArray temp_group, best_group = null;
			
			if (!(ASEval is SubsetEvaluator))
			{
				throw new System.Exception(ASEval.GetType().FullName + " is not a " + "Subset evaluator!");
			}
			
			m_SubsetEval = ASEval;
			m_Instances = data;
			m_numAttribs = m_Instances.numAttributes();
			
			/*    if (m_ASEval instanceof AttributeTransformer) {
			throw new Exception("Can't use an attribute transformer "
			+"with RankSearch");
			} */
			if (m_ASEval is UnsupervisedAttributeEvaluator || m_ASEval is UnsupervisedSubsetEvaluator)
			{
				m_hasClass = false;
				/*      if (!(m_SubsetEval instanceof UnsupervisedSubsetEvaluator)) {
				throw new Exception("Must use an unsupervised subset evaluator.");
				} */
			}
			else
			{
				m_hasClass = true;
				m_classIndex = m_Instances.classIndex();
			}
			
			if (m_ASEval is AttributeEvaluator)
			{
				// generate the attribute ranking first
				Ranker ranker = new Ranker();
				((AttributeEvaluator) m_ASEval).buildEvaluator(m_Instances);
				if (m_ASEval is AttributeTransformer)
				{
					// get the transformed data a rebuild the subset evaluator
					m_Instances = ((AttributeTransformer) m_ASEval).transformedData();
					((SubsetEvaluator) m_SubsetEval).buildEvaluator(m_Instances);
				}
				m_Ranking = ranker.search((AttributeEvaluator) m_ASEval, m_Instances);
			}
			else
			{
				GreedyStepwise fs = new GreedyStepwise();
				double[][] rankres;
				fs.GenerateRanking = true;
				((SubsetEvaluator) m_ASEval).buildEvaluator(m_Instances);
				fs.search(m_ASEval, m_Instances);
				rankres = fs.rankedAttributes();
				m_Ranking = new int[rankres.Length];
				for (int i = 0; i < rankres.Length; i++)
				{
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					m_Ranking[i] = (int) rankres[i][0];
				}
			}
			
			// now evaluate the attribute ranking
			for (int i = 0; i < m_Ranking.Length; i++)
			{
				temp_group = new System.Collections.BitArray((m_numAttribs % 64 == 0?m_numAttribs / 64:m_numAttribs / 64 + 1) * 64);
				for (int j = 0; j <= i; j++)
				{
					//SupportClass.BitArraySupport.Set(temp_group, m_Ranking[j]);
                    temp_group.Set(m_Ranking[j], true);
				}
				temp_merit = ((SubsetEvaluator) m_SubsetEval).evaluateSubset(temp_group);
				
				if (temp_merit > best_merit)
				{
					best_merit = temp_merit; ;
					best_group = temp_group;
				}
			}
			m_bestMerit = best_merit;
			return attributeList(best_group);
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
		
		/// <summary> returns a description of the search as a String</summary>
		/// <returns> a description of the search
		/// </returns>
		public override System.String ToString()
		{
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			text.Append("\tRankSearch :\n");
			text.Append("\tAttribute evaluator : " + AttributeEvaluator.GetType().FullName + " ");
			if (m_ASEval is OptionHandler)
			{
				System.String[] evaluatorOptions = new System.String[0];
				evaluatorOptions = ((OptionHandler) m_ASEval).Options;
				for (int i = 0; i < evaluatorOptions.Length; i++)
				{
					text.Append(evaluatorOptions[i] + ' ');
				}
			}
			text.Append("\n");
			text.Append("\tAttribute ranking : \n");
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			int rlength = (int) (System.Math.Log(m_Ranking.Length) / System.Math.Log(10) + 1);
			for (int i = 0; i < m_Ranking.Length; i++)
			{
				text.Append("\t " + Utils.doubleToString((double) (m_Ranking[i] + 1), rlength, 0) + " " + m_Instances.attribute(m_Ranking[i]).name() + '\n');
			}
			text.Append("\tMerit of best subset found : ");
			int fieldwidth = 3;
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			double precision = (m_bestMerit - (int) m_bestMerit);
			if (System.Math.Abs(m_bestMerit) > 0)
			{
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				fieldwidth = (int) System.Math.Abs((System.Math.Log(System.Math.Abs(m_bestMerit)) / System.Math.Log(10))) + 2;
			}
			if (System.Math.Abs(precision) > 0)
			{
				precision = System.Math.Abs((System.Math.Log(System.Math.Abs(precision)) / System.Math.Log(10))) + 3;
			}
			else
			{
				precision = 2;
			}
			
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			text.Append(Utils.doubleToString(System.Math.Abs(m_bestMerit), fieldwidth + (int) precision, (int) precision) + "\n");
			return text.ToString();
		}
	}
}