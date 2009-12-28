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
*    GainRatioAttributeEval.java
*    Copyright (C) 1999 Mark Hall
*
*/
using System;
//UPGRADE_TODO: The package 'weka.core' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using weka.core;
//UPGRADE_TODO: The type 'weka.filters.supervised.attribute.Discretize' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using Discretize = weka.filters.supervised.attribute.Discretize;
//UPGRADE_TODO: The type 'weka.filters.Filter' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using Filter = weka.filters.Filter;
namespace weka.attributeSelection
{
	
	/// <summary> Class for Evaluating attributes individually by measuring gain ratio 
	/// with respect to the class. <p>
	/// 
	/// Valid options are:<p>
	/// 
	/// -M <br>
	/// Treat missing values as a seperate value. <br>
	/// 
	/// </summary>
	/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.16 $
	/// </version>
	[Serializable]
	public class GainRatioAttributeEval:AttributeEvaluator, OptionHandler
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the current settings of WrapperSubsetEval.</summary>
		/// <returns> an array of strings suitable for passing to setOptions()
		/// </returns>
		/// <summary> Parses a given list of options. Valid options are:<p>
		/// 
		/// -M <br>
		/// Treat missing values as a seperate value. <p>
		/// 
		/// </summary>
		/// <param name="options">the list of options as an array of strings
		/// </param>
		/// <exception cref="Exception">if an option is not supported
		/// 
		/// </exception>
		virtual public System.String[] Options
		{
			get
			{
				System.String[] options = new System.String[1];
				int current = 0;
				
				if (!MissingMerge)
				{
					options[current++] = "-M";
				}
				
				while (current < options.Length)
				{
					options[current++] = "";
				}
				
				return options;
			}
			
			set
			{
				resetOptions();
				MissingMerge = !(Utils.getFlag('M', value));
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> get whether missing values are being distributed or not
		/// 
		/// </summary>
		/// <returns> true if missing values are being distributed.
		/// </returns>
		/// <summary> distribute the counts for missing values across observed values
		/// 
		/// </summary>
		/// <param name="b">true=distribute missing values.
		/// </param>
		virtual public bool MissingMerge
		{
			get
			{
				return m_missing_merge;
			}
			
			set
			{
				m_missing_merge = value;
			}
			
		}
		
		/// <summary>The training instances </summary>
		private Instances m_trainInstances;
		
		/// <summary>The class index </summary>
		private int m_classIndex;
		
		/// <summary>The number of attributes </summary>
		private int m_numAttribs;
		
		/// <summary>The number of instances </summary>
		private int m_numInstances;
		
		/// <summary>The number of classes </summary>
		private int m_numClasses;
		
		/// <summary>Merge missing values </summary>
		private bool m_missing_merge;
		
		/// <summary> Returns a string describing this attribute evaluator</summary>
		/// <returns> a description of the evaluator suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String globalInfo()
		{
			return "GainRatioAttributeEval :\n\nEvaluates the worth of an attribute " + "by measuring the gain ratio with respect to the class.\n\n" + "GainR(Class, Attribute) = (H(Class) - H(Class | Attribute)) / " + "H(Attribute).\n";
		}
		
		/// <summary> Constructor</summary>
		public GainRatioAttributeEval()
		{
			resetOptions();
		}
		
		
		/// <summary> Returns an enumeration describing the available options.</summary>
		/// <returns> an enumeration of all the available options.
		/// 
		/// </returns>
		public virtual System.Collections.IEnumerator listOptions()
		{
			System.Collections.ArrayList newVector = System.Collections.ArrayList.Synchronized(new System.Collections.ArrayList(1));
			newVector.Add(new Option("\ttreat missing values as a seperate " + "value.", "M", 0, "-M"));
			return newVector.GetEnumerator();
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String missingMergeTipText()
		{
			return "Distribute counts for missing values. Counts are distributed " + "across other values in proportion to their frequency. Otherwise, " + "missing is treated as a separate value.";
		}
		
		
		/// <summary> Initializes a gain ratio attribute evaluator.
		/// Discretizes all attributes that are numeric.
		/// 
		/// </summary>
		/// <param name="data">set of instances serving as training data 
		/// </param>
		/// <exception cref="Exception">if the evaluator has not been 
		/// generated successfully
		/// </exception>
		public override void  buildEvaluator(Instances data)
		{
			if (data.checkForStringAttributes())
			{
				throw new Exception("Can't handle string attributes!");
			}
			
			m_trainInstances = data;
			m_classIndex = m_trainInstances.classIndex();
			m_numAttribs = m_trainInstances.numAttributes();
			m_numInstances = m_trainInstances.numInstances();
			
			if (m_trainInstances.attribute(m_classIndex).Numeric)
			{
				throw new System.Exception("Class must be nominal!");
			}
			
			Discretize disTransform = new Discretize();
			disTransform.UseBetterEncoding=true;
			disTransform.setInputFormat(m_trainInstances);
			m_trainInstances = Filter.useFilter(m_trainInstances, disTransform);
			m_numClasses = m_trainInstances.attribute(m_classIndex).numValues();
		}
		
		
		/// <summary> reset options to default values</summary>
		protected internal virtual void  resetOptions()
		{
			m_trainInstances = null;
			m_missing_merge = true;
		}
		
		
		/// <summary> evaluates an individual attribute by measuring the gain ratio
		/// of the class given the attribute.
		/// 
		/// </summary>
		/// <param name="attribute">the index of the attribute to be evaluated
		/// </param>
		/// <exception cref="Exception">if the attribute could not be evaluated
		/// </exception>
		public override double evaluateAttribute(int attribute)
		{
			int i, j, ii, jj;
			int nnj, nni, ni, nj;
			double sum = 0.0;
			ni = m_trainInstances.attribute(attribute).numValues() + 1;
			nj = m_numClasses + 1;
			double[] sumi, sumj;
			Instance inst;
			double temp = 0.0;
			sumi = new double[ni];
			sumj = new double[nj];
			double[][] counts = new double[ni][];
			for (int i2 = 0; i2 < ni; i2++)
			{
				counts[i2] = new double[nj];
			}
			sumi = new double[ni];
			sumj = new double[nj];
			
			for (i = 0; i < ni; i++)
			{
				sumi[i] = 0.0;
				
				for (j = 0; j < nj; j++)
				{
					sumj[j] = 0.0;
					counts[i][j] = 0.0;
				}
			}
			
			// Fill the contingency table
			for (i = 0; i < m_numInstances; i++)
			{
				inst = m_trainInstances.instance(i);
				
				if (inst.isMissing(attribute))
				{
					ii = ni - 1;
				}
				else
				{
					ii = (int) inst.value_Renamed(attribute);
				}
				
				if (inst.isMissing(m_classIndex))
				{
					jj = nj - 1;
				}
				else
				{
					jj = (int) inst.value_Renamed(m_classIndex);
				}
				
				counts[ii][jj]++;
			}
			
			// get the row totals
			for (i = 0; i < ni; i++)
			{
				sumi[i] = 0.0;
				
				for (j = 0; j < nj; j++)
				{
					sumi[i] += counts[i][j];
					sum += counts[i][j];
				}
			}
			
			// get the column totals
			for (j = 0; j < nj; j++)
			{
				sumj[j] = 0.0;
				
				for (i = 0; i < ni; i++)
				{
					sumj[j] += counts[i][j];
				}
			}
			
			// distribute missing counts
			if (m_missing_merge && (sumi[ni - 1] < m_numInstances) && (sumj[nj - 1] < m_numInstances))
			{
				double[] i_copy = new double[sumi.Length];
				double[] j_copy = new double[sumj.Length];
				double[][] tmpArray = new double[sumi.Length][];
				for (int i3 = 0; i3 < sumi.Length; i3++)
				{
					tmpArray[i3] = new double[sumj.Length];
				}
				double[][] counts_copy = tmpArray;
				
				for (i = 0; i < ni; i++)
				{
					Array.Copy(counts[i], 0, counts_copy[i], 0, sumj.Length);
				}
				
				Array.Copy(sumi, 0, i_copy, 0, sumi.Length);
				Array.Copy(sumj, 0, j_copy, 0, sumj.Length);
				double total_missing = (sumi[ni - 1] + sumj[nj - 1] - counts[ni - 1][nj - 1]);
				
				// do the missing i's
				if (sumi[ni - 1] > 0.0)
				{
					for (j = 0; j < nj - 1; j++)
					{
						if (counts[ni - 1][j] > 0.0)
						{
							for (i = 0; i < ni - 1; i++)
							{
								temp = ((i_copy[i] / (sum - i_copy[ni - 1])) * counts[ni - 1][j]);
								counts[i][j] += temp;
								sumi[i] += temp;
							}
							
							counts[ni - 1][j] = 0.0;
						}
					}
				}
				
				sumi[ni - 1] = 0.0;
				
				// do the missing j's
				if (sumj[nj - 1] > 0.0)
				{
					for (i = 0; i < ni - 1; i++)
					{
						if (counts[i][nj - 1] > 0.0)
						{
							for (j = 0; j < nj - 1; j++)
							{
								temp = ((j_copy[j] / (sum - j_copy[nj - 1])) * counts[i][nj - 1]);
								counts[i][j] += temp;
								sumj[j] += temp;
							}
							
							counts[i][nj - 1] = 0.0;
						}
					}
				}
				
				sumj[nj - 1] = 0.0;
				
				// do the both missing
				if (counts[ni - 1][nj - 1] > 0.0 && total_missing != sum)
				{
					for (i = 0; i < ni - 1; i++)
					{
						for (j = 0; j < nj - 1; j++)
						{
							temp = (counts_copy[i][j] / (sum - total_missing)) * counts_copy[ni - 1][nj - 1];
							counts[i][j] += temp;
							sumi[i] += temp;
							sumj[j] += temp;
						}
					}
					
					counts[ni - 1][nj - 1] = 0.0;
				}
			}
			
			return ContingencyTables.gainRatio(counts);
		}
		
		
		/// <summary> Return a description of the evaluator</summary>
		/// <returns> description as a string
		/// </returns>
		public override System.String ToString()
		{
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			
			if (m_trainInstances == null)
			{
				text.Append("\tGain Ratio evaluator has not been built");
			}
			else
			{
				text.Append("\tGain Ratio feature evaluator");
				
				if (!m_missing_merge)
				{
					text.Append("\n\tMissing values treated as seperate");
				}
			}
			
			text.Append("\n");
			return text.ToString();
		}
		
		
		// ============
		// Test method.
		// ============
		/// <summary> Main method for testing this class.
		/// 
		/// </summary>
		/// <param name="args">the options
		/// -t training file
		/// </param>
		
		public static void  Main(System.String[] args)
		{
			try
			{
				System.Console.Out.WriteLine(AttributeSelection.SelectAttributes(new GainRatioAttributeEval(), args));
			}
			catch (System.Exception e)
			{
				//SupportClass.WriteStackTrace(e, Console.Error);
				//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Throwable.getMessage' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
				System.Console.Out.WriteLine(e.Message);
			}
		}
	}
}