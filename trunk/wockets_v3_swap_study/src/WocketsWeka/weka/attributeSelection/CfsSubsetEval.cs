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
*    CfsSubsetEval.java
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
	
	/// <summary> CFS attribute subset evaluator.
	/// For more information see: <p>
	/// 
	/// Hall, M. A. (1998). Correlation-based Feature Subset Selection for Machine 
	/// Learning. Thesis submitted in partial fulfilment of the requirements of the
	/// degree of Doctor of Philosophy at the University of Waikato. <p>
	/// 
	/// Valid options are:
	/// 
	/// -M <br>
	/// Treat missing values as a seperate value. <p>
	/// 
	/// -L <br>
	/// Don't include locally predictive attributes. <p>
	/// 
	/// </summary>
	/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.19.2.1 $
	/// </version>
	[Serializable]
	public class CfsSubsetEval:SubsetEvaluator, OptionHandler
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the current settings of CfsSubsetEval
		/// 
		/// </summary>
		/// <returns> an array of strings suitable for passing to setOptions()
		/// </returns>
		/// <summary> Parses and sets a given list of options. <p>
		/// 
		/// Valid options are:
		/// 
		/// -M <br>
		/// Treat missing values as a seperate value. <p>
		/// 
		/// -L <br>
		/// Don't include locally predictive attributes. <p>
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
				
				if (MissingSeperate)
				{
					options[current++] = "-M";
				}
				
				if (!LocallyPredictive)
				{
					options[current++] = "-L";
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
				MissingSeperate = Utils.getFlag('M', value);
				LocallyPredictive = !Utils.getFlag('L', value);
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Return true if including locally predictive attributes
		/// 
		/// </summary>
		/// <returns> true if locally predictive attributes are to be used
		/// </returns>
		/// <summary> Include locally predictive attributes
		/// 
		/// </summary>
		/// <param name="b">true or false
		/// </param>
		virtual public bool LocallyPredictive
		{
			get
			{
				return m_locallyPredictive;
			}
			
			set
			{
				m_locallyPredictive = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Return true is missing is treated as a seperate value
		/// 
		/// </summary>
		/// <returns> true if missing is to be treated as a seperate value
		/// </returns>
		/// <summary> Treat missing as a seperate value
		/// 
		/// </summary>
		/// <param name="b">true or false
		/// </param>
		virtual public bool MissingSeperate
		{
			get
			{
				return m_missingSeperate;
			}
			
			set
			{
				m_missingSeperate = value;
			}
			
		}
		
		/// <summary>The training instances </summary>
		private Instances m_trainInstances;
		/// <summary>Discretise attributes when class in nominal </summary>
		private Discretize m_disTransform;
		/// <summary>The class index </summary>
		private int m_classIndex;
		/// <summary>Is the class numeric </summary>
		private bool m_isNumeric;
		/// <summary>Number of attributes in the training data </summary>
		private int m_numAttribs;
		/// <summary>Number of instances in the training data </summary>
		private int m_numInstances;
		/// <summary>Treat missing values as seperate values </summary>
		private bool m_missingSeperate;
		/// <summary>Include locally predicitive attributes </summary>
		private bool m_locallyPredictive;
		/// <summary>Holds the matrix of attribute correlations </summary>
		//  private Matrix m_corr_matrix;
		private float[][] m_corr_matrix;
		/// <summary>Standard deviations of attributes (when using pearsons correlation) </summary>
		private double[] m_std_devs;
		/// <summary>Threshold for admitting locally predictive features </summary>
		private double m_c_Threshold;
		
		/// <summary> Returns a string describing this attribute evaluator</summary>
		/// <returns> a description of the evaluator suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String globalInfo()
		{
			return "CfsSubsetEval :\n\nEvaluates the worth of a subset of attributes " + "by considering the individual predictive ability of each feature " + "along with the degree of redundancy between them.\n\n" + "Subsets of features that are highly correlated with the class " + "while having low intercorrelation are preferred.\n";
		}
		
		/// <summary> Constructor</summary>
		public CfsSubsetEval()
		{
			resetOptions();
		}
		
		
		/// <summary> Returns an enumeration describing the available options.</summary>
		/// <returns> an enumeration of all the available options.
		/// 
		/// 
		/// </returns>
		public virtual System.Collections.IEnumerator listOptions()
		{
			System.Collections.ArrayList newVector = System.Collections.ArrayList.Synchronized(new System.Collections.ArrayList(3));
			newVector.Add(new Option("\tTreat missing values as a seperate" + "\n\tvalue.", "M", 0, "-M"));
			newVector.Add(new Option("\tDon't include locally predictive attributes" + ".", "L", 0, "-L"));
			return newVector.GetEnumerator();
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String locallyPredictiveTipText()
		{
			return "Identify locally predictive attributes. Iteratively adds " + "attributes with the highest correlation with the class as long " + "as there is not already an attribute in the subset that has a " + "higher correlation with the attribute in question";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String missingSeperateTipText()
		{
			return "Treat missing as a separate value. Otherwise, counts for missing " + "values are distributed across other values in proportion to their " + "frequency.";
		}
		
		
		/// <summary> Generates a attribute evaluator. Has to initialize all fields of the 
		/// evaluator that are not being set via options.
		/// 
		/// CFS also discretises attributes (if necessary) and initializes
		/// the correlation matrix.
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
			m_trainInstances.deleteWithMissingClass();
			m_classIndex = m_trainInstances.classIndex();
			m_numAttribs = m_trainInstances.numAttributes();
			m_numInstances = m_trainInstances.numInstances();
			m_isNumeric = m_trainInstances.attribute(m_classIndex).Numeric;
			
			if (!m_isNumeric)
			{
				m_disTransform = new Discretize();
				m_disTransform.UseBetterEncoding=true;
				m_disTransform.setInputFormat(m_trainInstances);
				m_trainInstances = Filter.useFilter(m_trainInstances, m_disTransform);
			}
			
			m_std_devs = new double[m_numAttribs];
			m_corr_matrix = new float[m_numAttribs][];
			for (int i = 0; i < m_numAttribs; i++)
			{
				m_corr_matrix[i] = new float[i + 1];
			}
			
			for (int i = 0; i < m_corr_matrix.Length; i++)
			{
				m_corr_matrix[i][i] = 1.0f;
				m_std_devs[i] = 1.0;
			}
			
			for (int i = 0; i < m_numAttribs; i++)
			{
				for (int j = 0; j < m_corr_matrix[i].Length - 1; j++)
				{
					m_corr_matrix[i][j] = - 999;
				}
			}
		}
		
		
		/// <summary> evaluates a subset of attributes
		/// 
		/// </summary>
		/// <param name="subset">a bitset representing the attribute subset to be 
		/// evaluated 
		/// </param>
		/// <exception cref="Exception">if the subset could not be evaluated
		/// </exception>
		public override double evaluateSubset(System.Collections.BitArray subset)
		{
			double num = 0.0;
			double denom = 0.0;
			float corr;
			int larger, smaller;
			// do numerator
			for (int i = 0; i < m_numAttribs; i++)
			{
				if (i != m_classIndex)
				{
					if (subset.Get(i))
					{
						if (i > m_classIndex)
						{
							larger = i; smaller = m_classIndex;
						}
						else
						{
							smaller = i; larger = m_classIndex;
						}
						/*	  int larger = (i > m_classIndex ? i : m_classIndex);
						int smaller = (i > m_classIndex ? m_classIndex : i); */
						if (m_corr_matrix[larger][smaller] == - 999)
						{
							corr = correlate(i, m_classIndex);
							m_corr_matrix[larger][smaller] = corr;
							num += (m_std_devs[i] * corr);
						}
						else
						{
							num += (m_std_devs[i] * m_corr_matrix[larger][smaller]);
						}
					}
				}
			}
			
			// do denominator
			for (int i = 0; i < m_numAttribs; i++)
			{
				if (i != m_classIndex)
				{
					if (subset.Get(i))
					{
						denom += (1.0 * m_std_devs[i] * m_std_devs[i]);
						
						for (int j = 0; j < m_corr_matrix[i].Length - 1; j++)
						{
							if (subset.Get(j))
							{
								if (m_corr_matrix[i][j] == - 999)
								{
									corr = correlate(i, j);
									m_corr_matrix[i][j] = corr;
									denom += (2.0 * m_std_devs[i] * m_std_devs[j] * corr);
								}
								else
								{
									denom += (2.0 * m_std_devs[i] * m_std_devs[j] * m_corr_matrix[i][j]);
								}
							}
						}
					}
				}
			}
			
			if (denom < 0.0)
			{
				denom *= (- 1.0);
			}
			
			if (denom == 0.0)
			{
				return (0.0);
			}
			
			double merit = (num / System.Math.Sqrt(denom));
			
			if (merit < 0.0)
			{
				merit *= (- 1.0);
			}
			
			return merit;
		}
		
		
		private float correlate(int att1, int att2)
		{
			if (!m_isNumeric)
			{
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				return (float) symmUncertCorr(att1, att2);
			}
			
			bool att1_is_num = (m_trainInstances.attribute(att1).Numeric);
			bool att2_is_num = (m_trainInstances.attribute(att2).Numeric);
			
			if (att1_is_num && att2_is_num)
			{
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				return (float) num_num(att1, att2);
			}
			else
			{
				if (att2_is_num)
				{
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					return (float) num_nom2(att1, att2);
				}
				else
				{
					if (att1_is_num)
					{
						//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
						return (float) num_nom2(att2, att1);
					}
				}
			}
			
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			return (float) nom_nom(att1, att2);
		}
		
		
		private double symmUncertCorr(int att1, int att2)
		{
			int i, j, k, ii, jj;
			int nnj, nni, ni, nj;
			double sum = 0.0;
			double[] sumi, sumj;
			double[][] counts;
			Instance inst;
			double corr_measure;
			bool flag = false;
			double temp = 0.0;
			
			if (att1 == m_classIndex || att2 == m_classIndex)
			{
				flag = true;
			}
			
			ni = m_trainInstances.attribute(att1).numValues() + 1;
			nj = m_trainInstances.attribute(att2).numValues() + 1;
			counts = new double[ni][];
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
				
				if (inst.isMissing(att1))
				{
					ii = ni - 1;
				}
				else
				{
					ii = (int) inst.value_Renamed(att1);
				}
				
				if (inst.isMissing(att2))
				{
					jj = nj - 1;
				}
				else
				{
					jj = (int) inst.value_Renamed(att2);
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
			if (!m_missingSeperate && (sumi[ni - 1] < m_numInstances) && (sumj[nj - 1] < m_numInstances))
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
			
			corr_measure = ContingencyTables.symmetricalUncertainty(counts);
			
			if (Utils.eq(corr_measure, 0.0))
			{
				if (flag == true)
				{
					return (0.0);
				}
				else
				{
					return (1.0);
				}
			}
			else
			{
				return (corr_measure);
			}
		}
		
		
		private double num_num(int att1, int att2)
		{
			int i;
			Instance inst;
			double r, diff1, diff2, num = 0.0, sx = 0.0, sy = 0.0;
			double mx = m_trainInstances.meanOrMode(m_trainInstances.attribute(att1));
			double my = m_trainInstances.meanOrMode(m_trainInstances.attribute(att2));
			
			for (i = 0; i < m_numInstances; i++)
			{
				inst = m_trainInstances.instance(i);
				diff1 = (inst.isMissing(att1))?0.0:(inst.value_Renamed(att1) - mx);
				diff2 = (inst.isMissing(att2))?0.0:(inst.value_Renamed(att2) - my);
				num += (diff1 * diff2);
				sx += (diff1 * diff1);
				sy += (diff2 * diff2);
			}
			
			if (sx != 0.0)
			{
				if (m_std_devs[att1] == 1.0)
				{
					m_std_devs[att1] = System.Math.Sqrt((sx / m_numInstances));
				}
			}
			
			if (sy != 0.0)
			{
				if (m_std_devs[att2] == 1.0)
				{
					m_std_devs[att2] = System.Math.Sqrt((sy / m_numInstances));
				}
			}
			
			if ((sx * sy) > 0.0)
			{
				r = (num / (System.Math.Sqrt(sx * sy)));
				return ((r < 0.0)?- r:r);
			}
			else
			{
				if (att1 != m_classIndex && att2 != m_classIndex)
				{
					return 1.0;
				}
				else
				{
					return 0.0;
				}
			}
		}
		
		
		private double num_nom2(int att1, int att2)
		{
			int i, ii, k;
			double temp;
			Instance inst;
			int mx = (int) m_trainInstances.meanOrMode(m_trainInstances.attribute(att1));
			double my = m_trainInstances.meanOrMode(m_trainInstances.attribute(att2));
			double stdv_num = 0.0;
			double diff1, diff2;
			double r = 0.0, rr, max_corr = 0.0;
			int nx = (!m_missingSeperate)?m_trainInstances.attribute(att1).numValues():m_trainInstances.attribute(att1).numValues() + 1;
			
			double[] prior_nom = new double[nx];
			double[] stdvs_nom = new double[nx];
			double[] covs = new double[nx];
			
			for (i = 0; i < nx; i++)
			{
				stdvs_nom[i] = covs[i] = prior_nom[i] = 0.0;
			}
			
			// calculate frequencies (and means) of the values of the nominal 
			// attribute
			for (i = 0; i < m_numInstances; i++)
			{
				inst = m_trainInstances.instance(i);
				
				if (inst.isMissing(att1))
				{
					if (!m_missingSeperate)
					{
						ii = mx;
					}
					else
					{
						ii = nx - 1;
					}
				}
				else
				{
					ii = (int) inst.value_Renamed(att1);
				}
				
				// increment freq for nominal
				prior_nom[ii]++;
			}
			
			for (k = 0; k < m_numInstances; k++)
			{
				inst = m_trainInstances.instance(k);
				// std dev of numeric attribute
				diff2 = (inst.isMissing(att2))?0.0:(inst.value_Renamed(att2) - my);
				stdv_num += (diff2 * diff2);
				
				// 
				for (i = 0; i < nx; i++)
				{
					if (inst.isMissing(att1))
					{
						if (!m_missingSeperate)
						{
							temp = (i == mx)?1.0:0.0;
						}
						else
						{
							temp = (i == (nx - 1))?1.0:0.0;
						}
					}
					else
					{
						temp = (i == inst.value_Renamed(att1))?1.0:0.0;
					}
					
					diff1 = (temp - (prior_nom[i] / m_numInstances));
					stdvs_nom[i] += (diff1 * diff1);
					covs[i] += (diff1 * diff2);
				}
			}
			
			// calculate weighted correlation
			for (i = 0, temp = 0.0; i < nx; i++)
			{
				// calculate the weighted variance of the nominal
				temp += ((prior_nom[i] / m_numInstances) * (stdvs_nom[i] / m_numInstances));
				
				if ((stdvs_nom[i] * stdv_num) > 0.0)
				{
					//System.out.println("Stdv :"+stdvs_nom[i]);
					rr = (covs[i] / (System.Math.Sqrt(stdvs_nom[i] * stdv_num)));
					
					if (rr < 0.0)
					{
						rr = - rr;
					}
					
					r += ((prior_nom[i] / m_numInstances) * rr);
				}
				/* if there is zero variance for the numeric att at a specific 
				level of the catergorical att then if neither is the class then 
				make this correlation at this level maximally bad i.e. 1.0. 
				If either is the class then maximally bad correlation is 0.0 */
				else
				{
					if (att1 != m_classIndex && att2 != m_classIndex)
					{
						r += ((prior_nom[i] / m_numInstances) * 1.0);
					}
				}
			}
			
			// set the standard deviations for these attributes if necessary
			// if ((att1 != classIndex) && (att2 != classIndex)) // =============
			if (temp != 0.0)
			{
				if (m_std_devs[att1] == 1.0)
				{
					m_std_devs[att1] = System.Math.Sqrt(temp);
				}
			}
			
			if (stdv_num != 0.0)
			{
				if (m_std_devs[att2] == 1.0)
				{
					m_std_devs[att2] = System.Math.Sqrt((stdv_num / m_numInstances));
				}
			}
			
			if (r == 0.0)
			{
				if (att1 != m_classIndex && att2 != m_classIndex)
				{
					r = 1.0;
				}
			}
			
			return r;
		}
		
		
		private double nom_nom(int att1, int att2)
		{
			int i, j, ii, jj, z;
			double temp1, temp2;
			Instance inst;
			int mx = (int) m_trainInstances.meanOrMode(m_trainInstances.attribute(att1));
			int my = (int) m_trainInstances.meanOrMode(m_trainInstances.attribute(att2));
			double diff1, diff2;
			double r = 0.0, rr, max_corr = 0.0;
			int nx = (!m_missingSeperate)?m_trainInstances.attribute(att1).numValues():m_trainInstances.attribute(att1).numValues() + 1;
			
			int ny = (!m_missingSeperate)?m_trainInstances.attribute(att2).numValues():m_trainInstances.attribute(att2).numValues() + 1;
			
			double[][] prior_nom = new double[nx][];
			for (int i2 = 0; i2 < nx; i2++)
			{
				prior_nom[i2] = new double[ny];
			}
			double[] sumx = new double[nx];
			double[] sumy = new double[ny];
			double[] stdvsx = new double[nx];
			double[] stdvsy = new double[ny];
			double[][] covs = new double[nx][];
			for (int i3 = 0; i3 < nx; i3++)
			{
				covs[i3] = new double[ny];
			}
			
			for (i = 0; i < nx; i++)
			{
				sumx[i] = stdvsx[i] = 0.0;
			}
			
			for (j = 0; j < ny; j++)
			{
				sumy[j] = stdvsy[j] = 0.0;
			}
			
			for (i = 0; i < nx; i++)
			{
				for (j = 0; j < ny; j++)
				{
					covs[i][j] = prior_nom[i][j] = 0.0;
				}
			}
			
			// calculate frequencies (and means) of the values of the nominal 
			// attribute
			for (i = 0; i < m_numInstances; i++)
			{
				inst = m_trainInstances.instance(i);
				
				if (inst.isMissing(att1))
				{
					if (!m_missingSeperate)
					{
						ii = mx;
					}
					else
					{
						ii = nx - 1;
					}
				}
				else
				{
					ii = (int) inst.value_Renamed(att1);
				}
				
				if (inst.isMissing(att2))
				{
					if (!m_missingSeperate)
					{
						jj = my;
					}
					else
					{
						jj = ny - 1;
					}
				}
				else
				{
					jj = (int) inst.value_Renamed(att2);
				}
				
				// increment freq for nominal
				prior_nom[ii][jj]++;
				sumx[ii]++;
				sumy[jj]++;
			}
			
			for (z = 0; z < m_numInstances; z++)
			{
				inst = m_trainInstances.instance(z);
				
				for (j = 0; j < ny; j++)
				{
					if (inst.isMissing(att2))
					{
						if (!m_missingSeperate)
						{
							temp2 = (j == my)?1.0:0.0;
						}
						else
						{
							temp2 = (j == (ny - 1))?1.0:0.0;
						}
					}
					else
					{
						temp2 = (j == inst.value_Renamed(att2))?1.0:0.0;
					}
					
					diff2 = (temp2 - (sumy[j] / m_numInstances));
					stdvsy[j] += (diff2 * diff2);
				}
				
				// 
				for (i = 0; i < nx; i++)
				{
					if (inst.isMissing(att1))
					{
						if (!m_missingSeperate)
						{
							temp1 = (i == mx)?1.0:0.0;
						}
						else
						{
							temp1 = (i == (nx - 1))?1.0:0.0;
						}
					}
					else
					{
						temp1 = (i == inst.value_Renamed(att1))?1.0:0.0;
					}
					
					diff1 = (temp1 - (sumx[i] / m_numInstances));
					stdvsx[i] += (diff1 * diff1);
					
					for (j = 0; j < ny; j++)
					{
						if (inst.isMissing(att2))
						{
							if (!m_missingSeperate)
							{
								temp2 = (j == my)?1.0:0.0;
							}
							else
							{
								temp2 = (j == (ny - 1))?1.0:0.0;
							}
						}
						else
						{
							temp2 = (j == inst.value_Renamed(att2))?1.0:0.0;
						}
						
						diff2 = (temp2 - (sumy[j] / m_numInstances));
						covs[i][j] += (diff1 * diff2);
					}
				}
			}
			
			// calculate weighted correlation
			for (i = 0; i < nx; i++)
			{
				for (j = 0; j < ny; j++)
				{
					if ((stdvsx[i] * stdvsy[j]) > 0.0)
					{
						//System.out.println("Stdv :"+stdvs_nom[i]);
						rr = (covs[i][j] / (System.Math.Sqrt(stdvsx[i] * stdvsy[j])));
						
						if (rr < 0.0)
						{
							rr = - rr;
						}
						
						r += ((prior_nom[i][j] / m_numInstances) * rr);
					}
					// if there is zero variance for either of the categorical atts then if
					// neither is the class then make this
					// correlation at this level maximally bad i.e. 1.0. If either is 
					// the class then maximally bad correlation is 0.0
					else
					{
						if (att1 != m_classIndex && att2 != m_classIndex)
						{
							r += ((prior_nom[i][j] / m_numInstances) * 1.0);
						}
					}
				}
			}
			
			// calculate weighted standard deviations for these attributes
			// (if necessary)
			for (i = 0, temp1 = 0.0; i < nx; i++)
			{
				temp1 += ((sumx[i] / m_numInstances) * (stdvsx[i] / m_numInstances));
			}
			
			if (temp1 != 0.0)
			{
				if (m_std_devs[att1] == 1.0)
				{
					m_std_devs[att1] = System.Math.Sqrt(temp1);
				}
			}
			
			for (j = 0, temp2 = 0.0; j < ny; j++)
			{
				temp2 += ((sumy[j] / m_numInstances) * (stdvsy[j] / m_numInstances));
			}
			
			if (temp2 != 0.0)
			{
				if (m_std_devs[att2] == 1.0)
				{
					m_std_devs[att2] = System.Math.Sqrt(temp2);
				}
			}
			
			if (r == 0.0)
			{
				if (att1 != m_classIndex && att2 != m_classIndex)
				{
					r = 1.0;
				}
			}
			
			return r;
		}
		
		
		/// <summary> returns a string describing CFS
		/// 
		/// </summary>
		/// <returns> the description as a string
		/// </returns>
		public override System.String ToString()
		{
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			
			if (m_trainInstances == null)
			{
				text.Append("CFS subset evaluator has not been built yet\n");
			}
			else
			{
				text.Append("\tCFS Subset Evaluator\n");
				
				if (m_missingSeperate)
				{
					text.Append("\tTreating missing values as a seperate value\n");
				}
				
				if (m_locallyPredictive)
				{
					text.Append("\tIncluding locally predictive attributes\n");
				}
			}
			
			return text.ToString();
		}
		
		
		private void  addLocallyPredictive(System.Collections.BitArray best_group)
		{
			int i, j;
			bool done = false;
			bool ok = true;
			double temp_best = - 1.0;
			float corr;
			j = 0;
			System.Collections.BitArray temp_group = (System.Collections.BitArray) best_group.Clone();
			int larger, smaller;
			
			while (!done)
			{
				temp_best = - 1.0;
				
				// find best not already in group
				for (i = 0; i < m_numAttribs; i++)
				{
					if (i > m_classIndex)
					{
						larger = i; smaller = m_classIndex;
					}
					else
					{
						smaller = i; larger = m_classIndex;
					}
					/*	int larger = (i > m_classIndex ? i : m_classIndex);
					int smaller = (i > m_classIndex ? m_classIndex : i); */
					if ((!temp_group.Get(i)) && (i != m_classIndex))
					{
						if (m_corr_matrix[larger][smaller] == - 999)
						{
							corr = correlate(i, m_classIndex);
							m_corr_matrix[larger][smaller] = corr;
						}
						
						if (m_corr_matrix[larger][smaller] > temp_best)
						{
							temp_best = m_corr_matrix[larger][smaller];
							j = i;
						}
					}
				}
				
				if (temp_best == - 1.0)
				{
					done = true;
				}
				else
				{
					ok = true;
					//SupportClass.BitArraySupport.Set(temp_group, j);
                    temp_group.Set(j, true);
					
					// check the best against correlations with others already
					// in group 
					for (i = 0; i < m_numAttribs; i++)
					{
						if (i > j)
						{
							larger = i; smaller = j;
						}
						else
						{
							larger = j; smaller = i;
						}
						/*  int larger = (i > j ? i : j);
						int smaller = (i > j ? j : i); */
						if (best_group.Get(i))
						{
							if (m_corr_matrix[larger][smaller] == - 999)
							{
								corr = correlate(i, j);
								m_corr_matrix[larger][smaller] = corr;
							}
							
							if (m_corr_matrix[larger][smaller] > temp_best - m_c_Threshold)
							{
								ok = false;
								break;
							}
						}
					}
					
					// if ok then add to best_group
					if (ok)
					{
						//SupportClass.BitArraySupport.Set(best_group, j);
                        best_group.Set(j, true);
					}
				}
			}
		}
		
		
		/// <summary> Calls locallyPredictive in order to include locally predictive
		/// attributes (if requested).
		/// 
		/// </summary>
		/// <param name="attributeSet">the set of attributes found by the search
		/// </param>
		/// <returns> a possibly ranked list of postprocessed attributes
		/// </returns>
		/// <exception cref="Exception">if postprocessing fails for some reason
		/// </exception>
		public override int[] postProcess(int[] attributeSet)
		{
			int j = 0;
			
			if (!m_locallyPredictive)
			{
				//      m_trainInstances = new Instances(m_trainInstances,0);
				return attributeSet;
			}
			
			System.Collections.BitArray bestGroup = new System.Collections.BitArray((m_numAttribs % 64 == 0?m_numAttribs / 64:m_numAttribs / 64 + 1) * 64);
			
			for (int i = 0; i < attributeSet.Length; i++)
			{
				//SupportClass.BitArraySupport.Set(bestGroup, attributeSet[i]);
                bestGroup.Set(attributeSet[i], true);
			}
			
			addLocallyPredictive(bestGroup);
			
			// count how many are set
			for (int i = 0; i < m_numAttribs; i++)
			{
				if (bestGroup.Get(i))
				{
					j++;
				}
			}
			
			int[] newSet = new int[j];
			j = 0;
			
			for (int i = 0; i < m_numAttribs; i++)
			{
				if (bestGroup.Get(i))
				{
					newSet[j++] = i;
				}
			}
			
			//    m_trainInstances = new Instances(m_trainInstances,0);
			return newSet;
		}
		
		
		protected internal virtual void  resetOptions()
		{
			m_trainInstances = null;
			m_missingSeperate = false;
			m_locallyPredictive = true;
			m_c_Threshold = 0.0;
		}
		
		
		/// <summary> Main method for testing this class.
		/// 
		/// </summary>
		/// <param name="args">the options
		/// </param>
		
		public static void  Main(System.String[] args)
		{
			try
			{
				System.Console.Out.WriteLine(AttributeSelection.SelectAttributes(new CfsSubsetEval(), args));
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