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
*    InfoGainAttributeEval.java
*    Copyright (C) 1999 Mark Hall
*
*/
using System;
//UPGRADE_TODO: The package 'weka.core' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using weka.core;
//UPGRADE_TODO: The type 'weka.filters.supervised.attribute.Discretize' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using Discretize = weka.filters.supervised.attribute.Discretize;
//UPGRADE_TODO: The type 'weka.filters.unsupervised.attribute.NumericToBinary' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using NumericToBinary = weka.filters.unsupervised.attribute.NumericToBinary;
//UPGRADE_TODO: The type 'weka.filters.Filter' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using Filter = weka.filters.Filter;
namespace weka.attributeSelection
{
	
	/// <summary> Class for Evaluating attributes individually by measuring information gain 
	/// with respect to the class.
	/// 
	/// Valid options are:<p>
	/// 
	/// -M <br>
	/// Treat missing values as a seperate value. <br>
	/// 
	/// -B <br>
	/// Just binarize numeric attributes instead of properly discretizing them. <br>
	/// 
	/// </summary>
	/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.14 $
	/// </version>
	[Serializable]
	public class InfoGainAttributeEval:AttributeEvaluator, OptionHandler
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the current settings of WrapperSubsetEval.
		/// 
		/// </summary>
		/// <returns> an array of strings suitable for passing to setOptions()
		/// </returns>
		/// <summary> Parses a given list of options. <p>
		/// 
		/// Valid options are:<p>
		/// 
		/// -M <br>
		/// Treat missing values as a seperate value. <br>
		/// 
		/// -B <br>
		/// Just binarize numeric attributes instead of properly discretizing them. <br>
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
				System.String[] options = new System.String[2];
				int current = 0;
				
				if (!MissingMerge)
				{
					options[current++] = "-M";
				}
				if (BinarizeNumericAttributes)
				{
					options[current++] = "-B";
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
				BinarizeNumericAttributes = Utils.getFlag('B', value);
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> get whether numeric attributes are just being binarized.
		/// 
		/// </summary>
		/// <returns> true if missing values are being distributed.
		/// </returns>
		/// <summary> Binarize numeric attributes.
		/// 
		/// </summary>
		/// <param name="b">true=binarize numeric attributes
		/// </param>
		virtual public bool BinarizeNumericAttributes
		{
			get
			{
				return m_Binarize;
			}
			
			set
			{
				m_Binarize = value;
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
		
		/// <summary>Treat missing values as a seperate value </summary>
		private bool m_missing_merge;
		
		/// <summary>Just binarize numeric attributes </summary>
		private bool m_Binarize;
		
		/// <summary>The info gain for each attribute </summary>
		private double[] m_InfoGains;
		
		/// <summary> Returns a string describing this attribute evaluator</summary>
		/// <returns> a description of the evaluator suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String globalInfo()
		{
			return "InfoGainAttributeEval :\n\nEvaluates the worth of an attribute " + "by measuring the information gain with respect to the class.\n\n" + "InfoGain(Class,Attribute) = H(Class) - H(Class | Attribute).\n";
		}
		
		/// <summary> Constructor</summary>
		public InfoGainAttributeEval()
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
			newVector.Add(new Option("\ttreat missing values as a seperate " + "value.", "M", 0, "-M"));
			newVector.Add(new Option("\tjust binarize numeric attributes instead\n " + "\tof properly discretizing them.", "B", 0, "-B"));
			return newVector.GetEnumerator();
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String binarizeNumericAttributesTipText()
		{
			return "Just binarize numeric attributes instead of properly discretizing them.";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String missingMergeTipText()
		{
			return "Distribute counts for missing values. Counts are distributed " + "across other values in proportion to their frequency. Otherwise, " + "missing is treated as a separate value.";
		}
		
		
		/// <summary> Initializes an information gain attribute evaluator.
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
			
			int classIndex = data.classIndex();
			if (data.attribute(classIndex).Numeric)
			{
				throw new System.Exception("Class must be nominal!");
			}
			int numInstances = data.numInstances();
			
			if (!m_Binarize)
			{
				Discretize disTransform = new Discretize();
				disTransform.UseBetterEncoding=true;
				disTransform.setInputFormat(data);
				data = Filter.useFilter(data, disTransform);
			}
			else
			{
				NumericToBinary binTransform = new NumericToBinary();
				binTransform.setInputFormat(data);
				data = Filter.useFilter(data, binTransform);
			}
			int numClasses = data.attribute(classIndex).numValues();
			
			// Reserve space and initialize counters
			double[][][] counts = new double[data.numAttributes()][][];
			for (int k = 0; k < data.numAttributes(); k++)
			{
				if (k != classIndex)
				{
					int numValues = data.attribute(k).numValues();
					double[][] tmpArray = new double[numValues + 1][];
					for (int i = 0; i < numValues + 1; i++)
					{
						tmpArray[i] = new double[numClasses + 1];
					}
					counts[k] = tmpArray;
				}
			}
			
			// Initialize counters
			double[] temp = new double[numClasses + 1];
			for (int k = 0; k < numInstances; k++)
			{
				Instance inst = data.instance(k);
				if (inst.classIsMissing())
				{
					temp[numClasses] += inst.weight();
				}
				else
				{
					temp[(int) inst.classValue()] += inst.weight();
				}
			}
			for (int k = 0; k < counts.Length; k++)
			{
				if (k != classIndex)
				{
					for (int i = 0; i < temp.Length; i++)
					{
						counts[k][0][i] = temp[i];
					}
				}
			}
			
			// Get counts
			for (int k = 0; k < numInstances; k++)
			{
				Instance inst = data.instance(k);
				for (int i = 0; i < inst.numValues(); i++)
				{
					if (inst.index(i) != classIndex)
					{
						if (inst.isMissingSparse(i) || inst.classIsMissing())
						{
							if (!inst.isMissingSparse(i))
							{
								counts[inst.index(i)][(int) inst.valueSparse(i)][numClasses] += inst.weight();
								counts[inst.index(i)][0][numClasses] -= inst.weight();
							}
							else if (!inst.classIsMissing())
							{
								counts[inst.index(i)][data.attribute(inst.index(i)).numValues()][(int) inst.classValue()] += inst.weight();
								counts[inst.index(i)][0][(int) inst.classValue()] -= inst.weight();
							}
							else
							{
								counts[inst.index(i)][data.attribute(inst.index(i)).numValues()][numClasses] += inst.weight();
								counts[inst.index(i)][0][numClasses] -= inst.weight();
							}
						}
						else
						{
							counts[inst.index(i)][(int) inst.valueSparse(i)][(int) inst.classValue()] += inst.weight();
							counts[inst.index(i)][0][(int) inst.classValue()] -= inst.weight();
						}
					}
				}
			}
			
			// distribute missing counts if required
			if (m_missing_merge)
			{
				
				for (int k = 0; k < data.numAttributes(); k++)
				{
					if (k != classIndex)
					{
						int numValues = data.attribute(k).numValues();
						
						// Compute marginals
						double[] rowSums = new double[numValues];
						double[] columnSums = new double[numClasses];
						double sum = 0;
						for (int i = 0; i < numValues; i++)
						{
							for (int j = 0; j < numClasses; j++)
							{
								rowSums[i] += counts[k][i][j];
								columnSums[j] += counts[k][i][j];
							}
							sum += rowSums[i];
						}
						
						if (Utils.gr(sum, 0))
						{
							double[][] tmpArray2 = new double[numValues][];
							for (int i2 = 0; i2 < numValues; i2++)
							{
								tmpArray2[i2] = new double[numClasses];
							}
							double[][] additions = tmpArray2;
							
							// Compute what needs to be added to each row
							for (int i = 0; i < numValues; i++)
							{
								for (int j = 0; j < numClasses; j++)
								{
									additions[i][j] = (rowSums[i] / sum) * counts[k][numValues][j];
								}
							}
							
							// Compute what needs to be added to each column
							for (int i = 0; i < numClasses; i++)
							{
								for (int j = 0; j < numValues; j++)
								{
									additions[j][i] += (columnSums[i] / sum) * counts[k][j][numClasses];
								}
							}
							
							// Compute what needs to be added to each cell
							for (int i = 0; i < numClasses; i++)
							{
								for (int j = 0; j < numValues; j++)
								{
									additions[j][i] += (counts[k][j][i] / sum) * counts[k][numValues][numClasses];
								}
							}
							
							// Make new contingency table
							double[][] tmpArray3 = new double[numValues][];
							for (int i3 = 0; i3 < numValues; i3++)
							{
								tmpArray3[i3] = new double[numClasses];
							}
							double[][] newTable = tmpArray3;
							for (int i = 0; i < numValues; i++)
							{
								for (int j = 0; j < numClasses; j++)
								{
									newTable[i][j] = counts[k][i][j] + additions[i][j];
								}
							}
							counts[k] = newTable;
						}
					}
				}
			}
			
			// Compute info gains
			m_InfoGains = new double[data.numAttributes()];
			for (int i = 0; i < data.numAttributes(); i++)
			{
				if (i != classIndex)
				{
					m_InfoGains[i] = (ContingencyTables.entropyOverColumns(counts[i]) - ContingencyTables.entropyConditionedOnRows(counts[i]));
				}
			}
		}
		
		/// <summary> Reset options to their default values</summary>
		protected internal virtual void  resetOptions()
		{
			m_InfoGains = null;
			m_missing_merge = true;
			m_Binarize = false;
		}
		
		
		/// <summary> evaluates an individual attribute by measuring the amount
		/// of information gained about the class given the attribute.
		/// 
		/// </summary>
		/// <param name="attribute">the index of the attribute to be evaluated
		/// </param>
		/// <exception cref="Exception">if the attribute could not be evaluated
		/// </exception>
		public override double evaluateAttribute(int attribute)
		{
			
			return m_InfoGains[attribute];
		}
		
		/// <summary> Describe the attribute evaluator</summary>
		/// <returns> a description of the attribute evaluator as a string
		/// </returns>
		public override System.String ToString()
		{
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			
			if (m_InfoGains == null)
			{
				text.Append("Information Gain attribute evaluator has not been built");
			}
			else
			{
				text.Append("\tInformation Gain Ranking Filter");
				if (!m_missing_merge)
				{
					text.Append("\n\tMissing values treated as seperate");
				}
				if (m_Binarize)
				{
					text.Append("\n\tNumeric attributes are just binarized");
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
		/// <param name="argv">the options
		/// </param>
		
		public static void  Main(System.String[] args)
		{
			try
			{
				System.Console.Out.WriteLine(AttributeSelection.SelectAttributes(new InfoGainAttributeEval(), args));
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