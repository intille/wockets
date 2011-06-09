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
*    Discretize.java
*    Copyright (C) 1999 Eibe Frank,Len Trigg
*
*/
using System;
using weka.filters;
using weka.core;
namespace weka.filters.supervised.attribute
{
	
	/// <summary> An instance filter that discretizes a range of numeric attributes in 
	/// the dataset into nominal attributes. Discretization is by 
	/// Fayyad & Irani's MDL method (the default).<p>
	/// 
	/// Valid filter-specific options are: <p>
	/// 
	/// -R col1,col2-col4,... <br>
	/// Specifies list of columns to Discretize. First
	/// and last are valid indexes. (default: none) <p>
	/// 
	/// -V <br>
	/// Invert matching sense.<p>
	/// 
	/// -D <br>
	/// Make binary nominal attributes. <p>
	/// 
	/// -E <br>
	/// Use better encoding of split point for MDL. <p>
	/// 
	/// -K <br>
	/// Use Kononeko's MDL criterion. <p>
	/// 
	/// </summary>
	/// <author>  Len Trigg (trigg@cs.waikato.ac.nz)
	/// </author>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.3 $
	/// </version>
	[Serializable]
	public class Discretize:Filter, SupervisedFilter, OptionHandler, WeightedInstancesHandler
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the current settings of the filter.
		/// 
		/// </summary>
		/// <returns> an array of strings suitable for passing to setOptions
		/// </returns>
		/// <summary> Parses the options for this object. Valid options are: <p>
		/// 
		/// -R col1,col2-col4,... <br>
		/// Specifies list of columns to Discretize. First
		/// and last are valid indexes. (default none) <p>
		/// 
		/// -V <br>
		/// Invert matching sense.<p>
		/// 
		/// -D <br>
		/// Make binary nominal attributes. <p>
		/// 
		/// -E <br>
		/// Use better encoding of split point for MDL. <p>
		/// 
		/// -K <br>
		/// Use Kononeko's MDL criterion. <p>
		/// 
		/// </summary>
		/// <param name="options">the list of options as an array of strings
		/// </param>
		/// <exception cref="Exception">if an option is not supported
		/// </exception>
		virtual public System.String[] Options
		{
			get
			{
				
				System.String[] options = new System.String[12];
				int current = 0;
				
				if (MakeBinary)
				{
					options[current++] = "-D";
				}
				if (UseBetterEncoding)
				{
					options[current++] = "-E";
				}
				if (UseKononenko)
				{
					options[current++] = "-K";
				}
				if (InvertSelection)
				{
					options[current++] = "-V";
				}
				if (!AttributeIndices.Equals(""))
				{
					options[current++] = "-R"; options[current++] = AttributeIndices;
				}
				while (current < options.Length)
				{
					options[current++] = "";
				}
				return options;
			}
			
			set
			{
				
				MakeBinary = Utils.getFlag('D', value);
				UseBetterEncoding = Utils.getFlag('E', value);
				UseKononenko = Utils.getFlag('K', value);
				InvertSelection = Utils.getFlag('V', value);
				
				System.String convertList = Utils.getOption('R', value);
				if (convertList.Length != 0)
				{
					AttributeIndices = convertList;
				}
				else
				{
					AttributeIndices = "first-last";
				}
				
				if (getInputFormat() != null)
				{
					setInputFormat(getInputFormat());
				}
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets whether binary attributes should be made for discretized ones.
		/// 
		/// </summary>
		/// <returns> true if attributes will be binarized
		/// </returns>
		/// <summary> Sets whether binary attributes should be made for discretized ones.
		/// 
		/// </summary>
		/// <param name="makeBinary">if binary attributes are to be made
		/// </param>
		virtual public bool MakeBinary
		{
			get
			{
				
				return m_MakeBinary;
			}
			
			set
			{
				
				m_MakeBinary = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets whether Kononenko's MDL criterion is to be used.
		/// 
		/// </summary>
		/// <returns> true if Kononenko's criterion will be used.
		/// </returns>
		/// <summary> Sets whether Kononenko's MDL criterion is to be used.
		/// 
		/// </summary>
		/// <param name="useKon">true if Kononenko's one is to be used
		/// </param>
		virtual public bool UseKononenko
		{
			get
			{
				
				return m_UseKononenko;
			}
			
			set
			{
				
				m_UseKononenko = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets whether better encoding is to be used for MDL.
		/// 
		/// </summary>
		/// <returns> true if the better MDL encoding will be used
		/// </returns>
		/// <summary> Sets whether better encoding is to be used for MDL.
		/// 
		/// </summary>
		/// <param name="useBetterEncoding">true if better encoding to be used.
		/// </param>
		virtual public bool UseBetterEncoding
		{
			get
			{
				
				return m_UseBetterEncoding;
			}
			
			set
			{
				
				m_UseBetterEncoding = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets whether the supplied columns are to be removed or kept
		/// 
		/// </summary>
		/// <returns> true if the supplied columns will be kept
		/// </returns>
		/// <summary> Sets whether selected columns should be removed or kept. If true the 
		/// selected columns are kept and unselected columns are deleted. If false
		/// selected columns are deleted and unselected columns are kept.
		/// 
		/// </summary>
		/// <param name="invert">the new invert setting
		/// </param>
		virtual public bool InvertSelection
		{
			get
			{
				
				return m_DiscretizeCols.Invert;
			}
			
			set
			{
				
				m_DiscretizeCols.Invert = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the current range selection
		/// 
		/// </summary>
		/// <returns> a string containing a comma separated list of ranges
		/// </returns>
		/// <summary> Sets which attributes are to be Discretized (only numeric
		/// attributes among the selection will be Discretized).
		/// 
		/// </summary>
		/// <param name="rangeList">a string representing the list of attributes. Since
		/// the string will typically come from a user, attributes are indexed from
		/// 1. <br>
		/// eg: first-3,5,6-last
		/// </param>
		/// <exception cref="IllegalArgumentException">if an invalid range list is supplied 
		/// </exception>
		virtual public System.String AttributeIndices
		{
			get
			{
				
				return m_DiscretizeCols.Ranges;
			}
			
			set
			{
				
				m_DiscretizeCols.Ranges = value;
			}
			
		}
		/// <summary> Sets which attributes are to be Discretized (only numeric
		/// attributes among the selection will be Discretized).
		/// 
		/// </summary>
		/// <param name="attributes">an array containing indexes of attributes to Discretize.
		/// Since the array will typically come from a program, attributes are indexed
		/// from 0.
		/// </param>
		/// <exception cref="IllegalArgumentException">if an invalid set of ranges
		/// is supplied 
		/// </exception>
		virtual public int[] AttributeIndicesArray
		{
			set
			{
				
				AttributeIndices = Range.indicesToRangeList(value);
			}
			
		}
		
		/// <summary>Stores which columns to Discretize </summary>
		protected internal Range m_DiscretizeCols = new Range();
		
		/// <summary>Store the current cutpoints </summary>
		protected internal double[][] m_CutPoints = null;
		
		/// <summary>Output binary attributes for discretized attributes. </summary>
		protected internal bool m_MakeBinary = false;
		
		/// <summary>Use better encoding of split point for MDL. </summary>
		protected internal bool m_UseBetterEncoding = false;
		
		/// <summary>Use Kononenko's MDL criterion instead of Fayyad et al.'s </summary>
		protected internal bool m_UseKononenko = false;
		
		/// <summary>Constructor - initialises the filter </summary>
		public Discretize()
		{
			
			AttributeIndices = "first-last";
		}
		
		
		/// <summary> Gets an enumeration describing the available options.
		/// 
		/// </summary>
		/// <returns> an enumeration of all the available options.
		/// </returns>
		public virtual System.Collections.IEnumerator listOptions()
		{
			
			System.Collections.ArrayList newVector = System.Collections.ArrayList.Synchronized(new System.Collections.ArrayList(7));
			
			newVector.Add(new Option("\tSpecifies list of columns to Discretize. First" + " and last are valid indexes.\n" + "\t(default none)", "R", 1, "-R <col1,col2-col4,...>"));
			
			newVector.Add(new Option("\tInvert matching sense of column indexes.", "V", 0, "-V"));
			
			newVector.Add(new Option("\tOutput binary attributes for discretized attributes.", "D", 0, "-D"));
			
			newVector.Add(new Option("\tUse better encoding of split point for MDL.", "E", 0, "-E"));
			
			newVector.Add(new Option("\tUse Kononenko's MDL criterion.", "K", 0, "-K"));
			
			return newVector.GetEnumerator();
		}
		
		
		/// <summary> Sets the format of the input instances.
		/// 
		/// </summary>
		/// <param name="instanceInfo">an Instances object containing the input instance
		/// structure (any instances contained in the object are ignored - only the
		/// structure is required).
		/// </param>
		/// <returns> true if the outputFormat may be collected immediately
		/// </returns>
		/// <exception cref="Exception">if the input format can't be set successfully
		/// </exception>
		public override bool setInputFormat(Instances instanceInfo)
		{
			
			base.setInputFormat(instanceInfo);
			
			m_DiscretizeCols.Upper = instanceInfo.numAttributes() - 1;
			m_CutPoints = null;
			
			if (instanceInfo.classIndex() < 0)
			{
				throw new Exception("Cannot use class-based discretization: " + "no class assigned to the dataset");
			}
			if (!instanceInfo.classAttribute().Nominal)
			{
				throw new Exception("Supervised discretization not possible:" + " class is not nominal!");
			}
			
			// If we implement loading cutfiles, then load 
			//them here and set the output format
			return false;
		}
		
		
		
		/// <summary> Input an instance for filtering. Ordinarily the instance is processed
		/// and made available for output immediately. Some filters require all
		/// instances be read before producing output.
		/// 
		/// </summary>
		/// <param name="instance">the input instance
		/// </param>
		/// <returns> true if the filtered instance may now be
		/// collected with output().
		/// </returns>
		/// <exception cref="IllegalStateException">if no input format has been defined.
		/// </exception>
		public override bool input(Instance instance)
		{
			
			if (getInputFormat() == null)
			{
				throw new System.SystemException("No input instance format defined");
			}
			if (m_NewBatch)
			{
				resetQueue();
				m_NewBatch = false;
			}
			
			if (m_CutPoints != null)
			{
				convertInstance(instance);
				return true;
			}
			
			bufferInput(instance);
			return false;
		}
		
		
		/// <summary> Signifies that this batch of input to the filter is finished. If the 
		/// filter requires all instances prior to filtering, output() may now 
		/// be called to retrieve the filtered instances.
		/// 
		/// </summary>
		/// <returns> true if there are instances pending output
		/// </returns>
		/// <exception cref="IllegalStateException">if no input structure has been defined
		/// </exception>
		public override bool batchFinished()
		{
			
			if (getInputFormat() == null)
			{
				throw new System.SystemException("No input instance format defined");
			}
			if (m_CutPoints == null)
			{
				calculateCutPoints();
				
				setOutputFormat();
				
				// If we implement saving cutfiles, save the cuts here
				
				// Convert pending input instances
				for (int i = 0; i < getInputFormat().numInstances(); i++)
				{
					convertInstance(getInputFormat().instance(i));
				}
			}
			flushInput();
			
			m_NewBatch = true;
			return (numPendingOutput() != 0);
		}
		
		/// <summary> Returns a string describing this filter
		/// 
		/// </summary>
		/// <returns> a description of the filter suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String globalInfo()
		{
			
			return "An instance filter that discretizes a range of numeric" + " attributes in the dataset into nominal attributes." + " Discretization is by Fayyad & Irani's MDL method (the default).";
		}
		
		/// <summary> Returns the tip text for this property
		/// 
		/// </summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String makeBinaryTipText()
		{
			
			return "Make resulting attributes binary.";
		}
		
		/// <summary> Returns the tip text for this property
		/// 
		/// </summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String useKononenkoTipText()
		{
			
			return "Use Kononenko's MDL criterion. If set to false" + " uses the Fayyad & Irani criterion.";
		}
		
		/// <summary> Returns the tip text for this property
		/// 
		/// </summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String useBetterEncodingTipText()
		{
			
			return "Uses a more efficient split point encoding.";
		}
		
		/// <summary> Returns the tip text for this property
		/// 
		/// </summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String invertSelectionTipText()
		{
			
			return "Set attribute selection mode. If false, only selected" + " (numeric) attributes in the range will be discretized; if" + " true, only non-selected attributes will be discretized.";
		}
		
		/// <summary> Returns the tip text for this property
		/// 
		/// </summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String attributeIndicesTipText()
		{
			return "Specify range of attributes to act on." + " This is a comma separated list of attribute indices, with" + " \"first\" and \"last\" valid values. Specify an inclusive" + " range with \"-\". E.g: \"first-3,5,6-10,last\".";
		}
		
		/// <summary> Gets the cut points for an attribute
		/// 
		/// </summary>
		/// <param name="the">index (from 0) of the attribute to get the cut points of
		/// </param>
		/// <returns> an array containing the cutpoints (or null if the
		/// attribute requested isn't being Discretized
		/// </returns>
		public virtual double[] getCutPoints(int attributeIndex)
		{
			
			if (m_CutPoints == null)
			{
				return null;
			}
			return m_CutPoints[attributeIndex];
		}
		
		/// <summary>Generate the cutpoints for each attribute </summary>
		protected internal virtual void  calculateCutPoints()
		{
			
			Instances copy = null;
			
			m_CutPoints = new double[getInputFormat().numAttributes()][];
			for (int i = getInputFormat().numAttributes() - 1; i >= 0; i--)
			{
				if ((m_DiscretizeCols.isInRange(i)) && (getInputFormat().attribute(i).Numeric))
				{
					
					// Use copy to preserve order
					if (copy == null)
					{
						copy = new Instances(getInputFormat());
					}
					calculateCutPointsByMDL(i, copy);
				}
			}
		}
		
		/// <summary> Set cutpoints for a single attribute using MDL.
		/// 
		/// </summary>
		/// <param name="index">the index of the attribute to set cutpoints for
		/// </param>
		protected internal virtual void  calculateCutPointsByMDL(int index, Instances data)
		{
			
			// Sort instances
			data.sort(data.attribute(index));
			
			// Find first instances that's missing
			int firstMissing = data.numInstances();
			for (int i = 0; i < data.numInstances(); i++)
			{
				if (data.instance(i).isMissing(index))
				{
					firstMissing = i;
					break;
				}
			}
			m_CutPoints[index] = cutPointsForSubset(data, index, 0, firstMissing);
		}
		
		/// <summary>Test using Kononenko's MDL criterion. </summary>
		private bool KononenkosMDL(double[] priorCounts, double[][] bestCounts, double numInstances, int numCutPoints)
		{
			
			double distPrior, instPrior, distAfter = 0, sum, instAfter = 0;
			double before, after;
			int numClassesTotal;
			
			// Number of classes occuring in the set
			numClassesTotal = 0;
			for (int i = 0; i < priorCounts.Length; i++)
			{
				if (priorCounts[i] > 0)
				{
					numClassesTotal++;
				}
			}
			
			// Encode distribution prior to split
			distPrior = SpecialFunctions.log2Binomial(numInstances + numClassesTotal - 1, numClassesTotal - 1);
			
			// Encode instances prior to split.
			instPrior = SpecialFunctions.log2Multinomial(numInstances, priorCounts);
			
			before = instPrior + distPrior;
			
			// Encode distributions and instances after split.
			for (int i = 0; i < bestCounts.Length; i++)
			{
				sum = Utils.sum(bestCounts[i]);
				distAfter += SpecialFunctions.log2Binomial(sum + numClassesTotal - 1, numClassesTotal - 1);
				instAfter += SpecialFunctions.log2Multinomial(sum, bestCounts[i]);
			}
			
			// Coding cost after split
			after = Utils.log2(numCutPoints) + distAfter + instAfter;
			
			// Check if split is to be accepted
			return (before > after);
		}
		
		
		/// <summary>Test using Fayyad and Irani's MDL criterion. </summary>
		private bool FayyadAndIranisMDL(double[] priorCounts, double[][] bestCounts, double numInstances, int numCutPoints)
		{
			
			double priorEntropy, entropy, gain;
			double entropyLeft, entropyRight, delta;
			int numClassesTotal, numClassesRight, numClassesLeft;
			
			// Compute entropy before split.
			priorEntropy = ContingencyTables.entropy(priorCounts);
			
			// Compute entropy after split.
			entropy = ContingencyTables.entropyConditionedOnRows(bestCounts);
			
			// Compute information gain.
			gain = priorEntropy - entropy;
			
			// Number of classes occuring in the set
			numClassesTotal = 0;
			for (int i = 0; i < priorCounts.Length; i++)
			{
				if (priorCounts[i] > 0)
				{
					numClassesTotal++;
				}
			}
			
			// Number of classes occuring in the left subset
			numClassesLeft = 0;
			for (int i = 0; i < bestCounts[0].Length; i++)
			{
				if (bestCounts[0][i] > 0)
				{
					numClassesLeft++;
				}
			}
			
			// Number of classes occuring in the right subset
			numClassesRight = 0;
			for (int i = 0; i < bestCounts[1].Length; i++)
			{
				if (bestCounts[1][i] > 0)
				{
					numClassesRight++;
				}
			}
			
			// Entropy of the left and the right subsets
			entropyLeft = ContingencyTables.entropy(bestCounts[0]);
			entropyRight = ContingencyTables.entropy(bestCounts[1]);
			
			// Compute terms for MDL formula
			delta = Utils.log2(System.Math.Pow(3, numClassesTotal) - 2) - (((double) numClassesTotal * priorEntropy) - (numClassesRight * entropyRight) - (numClassesLeft * entropyLeft));
			
			// Check if split is to be accepted
			return (gain > (Utils.log2(numCutPoints) + delta) / (double) numInstances);
		}
		
		
		/// <summary>Selects cutpoints for sorted subset. </summary>
		private double[] cutPointsForSubset(Instances instances, int attIndex, int first, int lastPlusOne)
		{
			
			double[][] counts, bestCounts;
			double[] priorCounts, left, right, cutPoints;
			//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
			double currentCutPoint = - System.Double.MaxValue, bestCutPoint = - 1, currentEntropy, bestEntropy, priorEntropy, gain;
			int bestIndex = - 1, numInstances = 0, numCutPoints = 0;
			
			// Compute number of instances in set
			if ((lastPlusOne - first) < 2)
			{
				return null;
			}
			
			// Compute class counts.
			counts = new double[2][];
			for (int i = 0; i < 2; i++)
			{
				counts[i] = new double[instances.numClasses()];
			}
			for (int i = first; i < lastPlusOne; i++)
			{
				numInstances = (int) (numInstances + instances.instance(i).weight());
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				counts[1][(int) instances.instance(i).classValue()] += instances.instance(i).weight();
			}
			
			// Save prior counts
			priorCounts = new double[instances.numClasses()];
			Array.Copy(counts[1], 0, priorCounts, 0, instances.numClasses());
			
			// Entropy of the full set
			priorEntropy = ContingencyTables.entropy(priorCounts);
			bestEntropy = priorEntropy;
			
			// Find best entropy.
			bestCounts = new double[2][];
			for (int i2 = 0; i2 < 2; i2++)
			{
				bestCounts[i2] = new double[instances.numClasses()];
			}
			for (int i = first; i < (lastPlusOne - 1); i++)
			{
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				counts[0][(int) instances.instance(i).classValue()] += instances.instance(i).weight();
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				counts[1][(int) instances.instance(i).classValue()] -= instances.instance(i).weight();
				if (instances.instance(i).value_Renamed(attIndex) < instances.instance(i + 1).value_Renamed(attIndex))
				{
					currentCutPoint = (instances.instance(i).value_Renamed(attIndex) + instances.instance(i + 1).value_Renamed(attIndex)) / 2.0;
					currentEntropy = ContingencyTables.entropyConditionedOnRows(counts);
					if (currentEntropy < bestEntropy)
					{
						bestCutPoint = currentCutPoint;
						bestEntropy = currentEntropy;
						bestIndex = i;
						Array.Copy(counts[0], 0, bestCounts[0], 0, instances.numClasses());
						Array.Copy(counts[1], 0, bestCounts[1], 0, instances.numClasses());
					}
					numCutPoints++;
				}
			}
			
			// Use worse encoding?
			if (!m_UseBetterEncoding)
			{
				numCutPoints = (lastPlusOne - first) - 1;
			}
			
			// Checks if gain is zero
			gain = priorEntropy - bestEntropy;
			if (gain <= 0)
			{
				return null;
			}
			
			// Check if split is to be accepted
			if ((m_UseKononenko && KononenkosMDL(priorCounts, bestCounts, numInstances, numCutPoints)) || (!m_UseKononenko && FayyadAndIranisMDL(priorCounts, bestCounts, numInstances, numCutPoints)))
			{
				
				// Select split points for the left and right subsets
				left = cutPointsForSubset(instances, attIndex, first, bestIndex + 1);
				right = cutPointsForSubset(instances, attIndex, bestIndex + 1, lastPlusOne);
				
				// Merge cutpoints and return them
				if ((left == null) && (right) == null)
				{
					cutPoints = new double[1];
					cutPoints[0] = bestCutPoint;
				}
				else if (right == null)
				{
					cutPoints = new double[left.Length + 1];
					Array.Copy(left, 0, cutPoints, 0, left.Length);
					cutPoints[left.Length] = bestCutPoint;
				}
				else if (left == null)
				{
					cutPoints = new double[1 + right.Length];
					cutPoints[0] = bestCutPoint;
					Array.Copy(right, 0, cutPoints, 1, right.Length);
				}
				else
				{
					cutPoints = new double[left.Length + right.Length + 1];
					Array.Copy(left, 0, cutPoints, 0, left.Length);
					cutPoints[left.Length] = bestCutPoint;
					Array.Copy(right, 0, cutPoints, left.Length + 1, right.Length);
				}
				
				return cutPoints;
			}
			else
				return null;
		}
		
		/// <summary> Set the output format. Takes the currently defined cutpoints and 
		/// m_InputFormat and calls setOutputFormat(Instances) appropriately.
		/// </summary>
		protected internal virtual void  setOutputFormat()
		{
			
			if (m_CutPoints == null)
			{
				setOutputFormat(null);
				return ;
			}
			FastVector attributes = new FastVector(getInputFormat().numAttributes());
			int classIndex = getInputFormat().classIndex();
			for (int i = 0; i < getInputFormat().numAttributes(); i++)
			{
				if ((m_DiscretizeCols.isInRange(i)) && (getInputFormat().attribute(i).Numeric))
				{
					if (!m_MakeBinary)
					{
						FastVector attribValues = new FastVector(1);
						if (m_CutPoints[i] == null)
						{
							attribValues.addElement("'All'");
						}
						else
						{
							for (int j = 0; j <= m_CutPoints[i].Length; j++)
							{
								if (j == 0)
								{
									attribValues.addElement("'(-inf-" + Utils.doubleToString(m_CutPoints[i][j], 6) + "]'");
								}
								else if (j == m_CutPoints[i].Length)
								{
									attribValues.addElement("'(" + Utils.doubleToString(m_CutPoints[i][j - 1], 6) + "-inf)'");
								}
								else
								{
									attribValues.addElement("'(" + Utils.doubleToString(m_CutPoints[i][j - 1], 6) + "-" + Utils.doubleToString(m_CutPoints[i][j], 6) + "]'");
								}
							}
						}
                        attributes.addElement(new weka.core.Attribute(getInputFormat().attribute(i).name(), attribValues));
					}
					else
					{
						if (m_CutPoints[i] == null)
						{
							FastVector attribValues = new FastVector(1);
							attribValues.addElement("'All'");
                            attributes.addElement(new weka.core.Attribute(getInputFormat().attribute(i).name(), attribValues));
						}
						else
						{
							if (i < getInputFormat().classIndex())
							{
								classIndex += m_CutPoints[i].Length - 1;
							}
							for (int j = 0; j < m_CutPoints[i].Length; j++)
							{
								FastVector attribValues = new FastVector(2);
								attribValues.addElement("'(-inf-" + Utils.doubleToString(m_CutPoints[i][j], 6) + "]'");
								attribValues.addElement("'(" + Utils.doubleToString(m_CutPoints[i][j], 6) + "-inf)'");
                                attributes.addElement(new weka.core.Attribute(getInputFormat().attribute(i).name(), attribValues));
							}
						}
					}
				}
				else
				{
					attributes.addElement(getInputFormat().attribute(i).copy());
				}
			}
			Instances outputFormat = new Instances(getInputFormat().relationName(), attributes, 0);
			outputFormat.ClassIndex = classIndex;
			setOutputFormat(outputFormat);
		}
		
		/// <summary> Convert a single instance over. The converted instance is added to 
		/// the end of the output queue.
		/// 
		/// </summary>
		/// <param name="instance">the instance to convert
		/// </param>
		protected internal virtual void  convertInstance(Instance instance)
		{
			
			int index = 0;
			double[] vals = new double[outputFormatPeek().numAttributes()];
			// Copy and convert the values
			for (int i = 0; i < getInputFormat().numAttributes(); i++)
			{
				if (m_DiscretizeCols.isInRange(i) && getInputFormat().attribute(i).Numeric)
				{
					int j;
					double currentVal = instance.value_Renamed(i);
					if (m_CutPoints[i] == null)
					{
						if (instance.isMissing(i))
						{
							vals[index] = Instance.missingValue();
						}
						else
						{
							vals[index] = 0;
						}
						index++;
					}
					else
					{
						if (!m_MakeBinary)
						{
							if (instance.isMissing(i))
							{
								vals[index] = Instance.missingValue();
							}
							else
							{
								for (j = 0; j < m_CutPoints[i].Length; j++)
								{
									if (currentVal <= m_CutPoints[i][j])
									{
										break;
									}
								}
								vals[index] = j;
							}
							index++;
						}
						else
						{
							for (j = 0; j < m_CutPoints[i].Length; j++)
							{
								if (instance.isMissing(i))
								{
									vals[index] = Instance.missingValue();
								}
								else if (currentVal <= m_CutPoints[i][j])
								{
									vals[index] = 0;
								}
								else
								{
									vals[index] = 1;
								}
								index++;
							}
						}
					}
				}
				else
				{
					vals[index] = instance.value_Renamed(i);
					index++;
				}
			}
			
			Instance inst = null;
			if (instance is SparseInstance)
			{
				inst = new SparseInstance(instance.weight(), vals);
			}
			else
			{
				inst = new Instance(instance.weight(), vals);
			}
			copyStringValues(inst, false, instance.dataset(), InputStringIndex, getOutputFormat(), OutputStringIndex);
			inst.Dataset = getOutputFormat();
			push(inst);
		}
		

	}
}