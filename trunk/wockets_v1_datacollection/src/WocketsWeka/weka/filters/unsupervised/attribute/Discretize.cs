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
namespace weka.filters.unsupervised.attribute
{
	
	/// <summary> An instance filter that discretizes a range of numeric attributes in 
	/// the dataset into nominal attributes. Discretization is by simple binning.
	/// Skips the class attribute if set.<p>
	/// 
	/// Valid filter-specific options are: <p>
	/// 
	/// -B num <br>
	/// Specifies the (maximum) number of bins to divide numeric attributes into.
	/// Default = 10.<p>
	/// 
	/// -M num <br>
	/// Specifies the desired weight of instances per bin for equal-frequency
	/// binning. If this is set to a positive number then the -B option will be 
	/// ignored. Default = -1.<p>
	/// 
	/// -F <br>
	/// Use equal-frequency instead of equal-width discretization if 
	/// class-based discretisation is turned off.<p>
	/// 
	/// -O <br>
	/// Optimize the number of bins using a leave-one-out estimate of the 
	/// entropy (for equal-width binning). If this is set then the -B option
	/// will be ignored.<p>
	/// 
	/// -R col1,col2-col4,... <br>
	/// Specifies list of columns to Discretize. First
	/// and last are valid indexes. (default: first-last) <p>
	/// 
	/// -V <br>
	/// Invert matching sense.<p>
	/// 
	/// -D <br>
	/// Make binary nominal attributes. <p>
	/// 
	/// </summary>
	/// <author>  Len Trigg (trigg@cs.waikato.ac.nz)
	/// </author>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.6.2.1 $
	/// </version>
	[Serializable]
	public class Discretize:PotentialClassIgnorer, UnsupervisedFilter, OptionHandler, WeightedInstancesHandler
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the current settings of the filter.
		/// 
		/// </summary>
		/// <returns> an array of strings suitable for passing to setOptions
		/// </returns>
		/// <summary> Parses the options for this object. Valid options are: <p>
		/// 
		/// -B num <br>
		/// Specifies the (maximum) number of bins to divide numeric attributes into.
		/// Default = 10.<p>
		/// 
		/// -M num <br>
		/// Specifies the desired weight of instances per bin for equal-frequency
		/// binning. If this is set to a positive number then the -B option will be 
		/// ignored. Default = -1.<p>
		/// 
		/// -F <br>
		/// Use equal-frequency instead of equal-width discretization if 
		/// class-based discretisation is turned off.<p>
		/// 
		/// -O <br>
		/// Optimize the number of bins using a leave-one-out estimate of the 
		/// entropy (for equal-width binning). If this is set then the -B
		/// option will be ignored.<p>
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
		/// </summary>
		/// <param name="options">the list of options as an array of strings
		/// </param>
		/// <exception cref="Exception">if an option is not supported
		/// </exception>
		virtual public System.String[] Options
		{
			get
			{
				
				System.String[] options = new System.String[10];
				int current = 0;
				
				if (MakeBinary)
				{
					options[current++] = "-D";
				}
				if (UseEqualFrequency)
				{
					options[current++] = "-F";
				}
				if (FindNumBins)
				{
					options[current++] = "-O";
				}
				if (InvertSelection)
				{
					options[current++] = "-V";
				}
				options[current++] = "-B"; options[current++] = "" + Bins;
				options[current++] = "-M";
				options[current++] = "" + DesiredWeightOfInstancesPerInterval;
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
				UseEqualFrequency = Utils.getFlag('F', value);
				FindNumBins = Utils.getFlag('O', value);
				InvertSelection = Utils.getFlag('V', value);
				
				System.String weight = Utils.getOption('M', value);
				if (weight.Length != 0)
				{
					//UPGRADE_TODO: The differences in the format  of parameters for constructor 'java.lang.Double.Double'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
					DesiredWeightOfInstancesPerInterval = (System.Double.Parse(weight));
				}
				else
				{
					DesiredWeightOfInstancesPerInterval = - 1;
				}
				
				System.String numBins = Utils.getOption('B', value);
				if (numBins.Length != 0)
				{
					Bins = System.Int32.Parse(numBins);
				}
				else
				{
					Bins = 10;
				}
				
				System.String convertList = Utils.getOption('R', value);
				if (convertList.Length != 0)
				{
					AttributeIndices = convertList;
				}
				else
				{
					AttributeIndices = m_DefaultCols;
				}
				
				if (getInputFormat() != null)
				{
					setInputFormat(getInputFormat());
				}
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Get the value of FindNumBins.
		/// 
		/// </summary>
		/// <returns> Value of FindNumBins.
		/// </returns>
		/// <summary> Set the value of FindNumBins.
		/// 
		/// </summary>
		/// <param name="newFindNumBins">Value to assign to FindNumBins.
		/// </param>
		virtual public bool FindNumBins
		{
			get
			{
				
				return m_FindNumBins;
			}
			
			set
			{
				
				m_FindNumBins = value;
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
		/// <summary> Get the DesiredWeightOfInstancesPerInterval value.</summary>
		/// <returns> the DesiredWeightOfInstancesPerInterval value.
		/// </returns>
		/// <summary> Set the DesiredWeightOfInstancesPerInterval value.</summary>
		/// <param name="newDesiredNumber">The new DesiredNumber value.
		/// </param>
		virtual public double DesiredWeightOfInstancesPerInterval
		{
			get
			{
				
				return m_DesiredWeightOfInstancesPerInterval;
			}
			
			set
			{
				
				m_DesiredWeightOfInstancesPerInterval = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Get the value of UseEqualFrequency.
		/// 
		/// </summary>
		/// <returns> Value of UseEqualFrequency.
		/// </returns>
		/// <summary> Set the value of UseEqualFrequency.
		/// 
		/// </summary>
		/// <param name="newUseEqualFrequency">Value to assign to UseEqualFrequency.
		/// </param>
		virtual public bool UseEqualFrequency
		{
			get
			{
				
				return m_UseEqualFrequency;
			}
			
			set
			{
				
				m_UseEqualFrequency = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the number of bins numeric attributes will be divided into
		/// 
		/// </summary>
		/// <returns> the number of bins.
		/// </returns>
		/// <summary> Sets the number of bins to divide each selected numeric attribute into
		/// 
		/// </summary>
		/// <param name="numBins">the number of bins
		/// </param>
		virtual public int Bins
		{
			get
			{
				
				return m_NumBins;
			}
			
			set
			{
				
				m_NumBins = value;
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
		
		/// <summary>The number of bins to divide the attribute into </summary>
		protected internal int m_NumBins = 10;
		
		/// <summary>The desired weight of instances per bin </summary>
		protected internal double m_DesiredWeightOfInstancesPerInterval = - 1;
		
		/// <summary>Store the current cutpoints </summary>
		protected internal double[][] m_CutPoints = null;
		
		/// <summary>Output binary attributes for discretized attributes. </summary>
		protected internal bool m_MakeBinary = false;
		
		/// <summary>Find the number of bins using cross-validated entropy. </summary>
		protected internal bool m_FindNumBins = false;
		
		/// <summary>Use equal-frequency binning if unsupervised discretization turned on </summary>
		protected internal bool m_UseEqualFrequency = false;
		
		/// <summary>The default columns to discretize </summary>
		protected internal System.String m_DefaultCols;
		
		/// <summary>Constructor - initialises the filter </summary>
		public Discretize()
		{
			
			m_DefaultCols = "first-last";
			AttributeIndices = "first-last";
		}
		
		/// <summary>Another constructor </summary>
		public Discretize(System.String cols)
		{
			
			m_DefaultCols = cols;
			AttributeIndices = cols;
		}
		
		/// <summary> Gets an enumeration describing the available options.
		/// 
		/// </summary>
		/// <returns> an enumeration of all the available options.
		/// </returns>
		public virtual System.Collections.IEnumerator listOptions()
		{
			
			System.Collections.ArrayList newVector = System.Collections.ArrayList.Synchronized(new System.Collections.ArrayList(7));
			
			newVector.Add(new Option("\tSpecifies the (maximum) number of bins to divide numeric" + " attributes into.\n" + "\t(default = 10)", "B", 1, "-B <num>"));
			
			newVector.Add(new Option("\tSpecifies the desired weight of instances per bin for\n" + "\tequal-frequency binning. If this is set to a positive\n" + "\tnumber then the -B option will be ignored.\n" + "\t(default = -1)", "M", 1, "-M <num>"));
			
			newVector.Add(new Option("\tUse equal-frequency instead of equal-width discretization.", "F", 0, "-F"));
			
			newVector.Add(new Option("\tOptimize number of bins using leave-one-out estimate\n" + "\tof estimated entropy (for equal-width discretization).\n" + "\tIf this is set then the -B option will be ignored.", "O", 0, "-O"));
			
			newVector.Add(new Option("\tSpecifies list of columns to Discretize. First" + " and last are valid indexes.\n" + "\t(default: first-last)", "R", 1, "-R <col1,col2-col4,...>"));
			
			newVector.Add(new Option("\tInvert matching sense of column indexes.", "V", 0, "-V"));
			
			newVector.Add(new Option("\tOutput binary attributes for discretized attributes.", "D", 0, "-D"));
			
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
			
			if (m_MakeBinary && m_IgnoreClass)
			{
				throw new System.ArgumentException("Can't ignore class when " + "changing the number of attributes!");
			}
			
			base.setInputFormat(instanceInfo);
			
			m_DiscretizeCols.Upper = instanceInfo.numAttributes() - 1;
			m_CutPoints = null;
			
			if (FindNumBins && UseEqualFrequency)
			{
				throw new System.ArgumentException("Bin number optimization in conjunction " + "with equal-frequency binning not implemented.");
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
			
			return "An instance filter that discretizes a range of numeric" + " attributes in the dataset into nominal attributes." + " Discretization is by simple binning. Skips the class" + " attribute if set.";
		}
		
		/// <summary> Returns the tip text for this property
		/// 
		/// </summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String findNumBinsTipText()
		{
			
			return "Optimize number of equal-width bins using leave-one-out. Doesn't " + "work for equal-frequency binning";
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
		public virtual System.String desiredWeightOfInstancesPerIntervalTipText()
		{
			
			return "Sets the desired weight of instances per interval for " + "equal-frequency binning.";
		}
		
		/// <summary> Returns the tip text for this property
		/// 
		/// </summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String useEqualFrequencyTipText()
		{
			
			return "If set to true, equal-frequency binning will be used instead of" + " equal-width binning.";
		}
		
		/// <summary> Returns the tip text for this property
		/// 
		/// </summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String binsTipText()
		{
			
			return "Number of bins.";
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
		/// attribute requested has been discretized into only one interval.)
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
				if ((m_DiscretizeCols.isInRange(i)) && (getInputFormat().attribute(i).Numeric) && (getInputFormat().classIndex() != i))
				{
					if (m_FindNumBins)
					{
						findNumBins(i);
					}
					else if (!m_UseEqualFrequency)
					{
						calculateCutPointsByEqualWidthBinning(i);
					}
					else
					{
						calculateCutPointsByEqualFrequencyBinning(i);
					}
				}
			}
		}
		
		/// <summary> Set cutpoints for a single attribute.
		/// 
		/// </summary>
		/// <param name="index">the index of the attribute to set cutpoints for
		/// </param>
		protected internal virtual void  calculateCutPointsByEqualWidthBinning(int index)
		{
			
			// Scan for max and min values
			double max = 0, min = 1, currentVal;
			Instance currentInstance;
			for (int i = 0; i < getInputFormat().numInstances(); i++)
			{
				currentInstance = getInputFormat().instance(i);
				if (!currentInstance.isMissing(index))
				{
					currentVal = currentInstance.value_Renamed(index);
					if (max < min)
					{
						max = min = currentVal;
					}
					if (currentVal > max)
					{
						max = currentVal;
					}
					if (currentVal < min)
					{
						min = currentVal;
					}
				}
			}
			double binWidth = (max - min) / m_NumBins;
			double[] cutPoints = null;
			if ((m_NumBins > 1) && (binWidth > 0))
			{
				cutPoints = new double[m_NumBins - 1];
				for (int i = 1; i < m_NumBins; i++)
				{
					cutPoints[i - 1] = min + binWidth * i;
				}
			}
			m_CutPoints[index] = cutPoints;
		}
		
		/// <summary> Set cutpoints for a single attribute.
		/// 
		/// </summary>
		/// <param name="index">the index of the attribute to set cutpoints for
		/// </param>
		protected internal virtual void  calculateCutPointsByEqualFrequencyBinning(int index)
		{
			
			// Copy data so that it can be sorted
			Instances data = new Instances(getInputFormat());
			
			// Sort input data
			data.sort(index);
			
			// Compute weight of instances without missing values
			double sumOfWeights = 0;
			for (int i = 0; i < data.numInstances(); i++)
			{
				if (data.instance(i).isMissing(index))
				{
					break;
				}
				else
				{
					sumOfWeights += data.instance(i).weight();
				}
			}
			double freq;
			double[] cutPoints = new double[m_NumBins - 1];
			if (DesiredWeightOfInstancesPerInterval > 0)
			{
				freq = DesiredWeightOfInstancesPerInterval;
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				cutPoints = new double[(int) (sumOfWeights / freq)];
			}
			else
			{
				freq = sumOfWeights / m_NumBins;
				cutPoints = new double[m_NumBins - 1];
			}
			
			// Compute break points
			double counter = 0, last = 0;
			int cpindex = 0, lastIndex = - 1;
			for (int i = 0; i < data.numInstances() - 1; i++)
			{
				
				// Stop if value missing
				if (data.instance(i).isMissing(index))
				{
					break;
				}
				counter += data.instance(i).weight();
				sumOfWeights -= data.instance(i).weight();
				
				// Do we have a potential breakpoint?
				if (data.instance(i).value_Renamed(index) < data.instance(i + 1).value_Renamed(index))
				{
					
					// Have we passed the ideal size?
					if (counter >= freq)
					{
						
						// Is this break point worse than the last one?
						if (((freq - last) < (counter - freq)) && (lastIndex != - 1))
						{
							cutPoints[cpindex] = (data.instance(lastIndex).value_Renamed(index) + data.instance(lastIndex + 1).value_Renamed(index)) / 2;
							counter -= last;
							last = counter;
							lastIndex = i;
						}
						else
						{
							cutPoints[cpindex] = (data.instance(i).value_Renamed(index) + data.instance(i + 1).value_Renamed(index)) / 2;
							counter = 0;
							last = 0;
							lastIndex = - 1;
						}
						cpindex++;
						freq = (sumOfWeights + counter) / ((cutPoints.Length + 1) - cpindex);
					}
					else
					{
						lastIndex = i;
						last = counter;
					}
				}
			}
			
			// Check whether there was another possibility for a cut point
			if ((cpindex < cutPoints.Length) && (lastIndex != - 1))
			{
				cutPoints[cpindex] = (data.instance(lastIndex).value_Renamed(index) + data.instance(lastIndex + 1).value_Renamed(index)) / 2;
				cpindex++;
			}
			
			// Did we find any cutpoints?
			if (cpindex == 0)
			{
				m_CutPoints[index] = null;
			}
			else
			{
				double[] cp = new double[cpindex];
				for (int i = 0; i < cpindex; i++)
				{
					cp[i] = cutPoints[i];
				}
				m_CutPoints[index] = cp;
			}
		}
		
		/// <summary> Optimizes the number of bins using leave-one-out cross-validation.
		/// 
		/// </summary>
		/// <param name="index">the attribute index
		/// </param>
		protected internal virtual void  findNumBins(int index)
		{
			
			//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
			double min = System.Double.MaxValue, max = - System.Double.MaxValue, binWidth = 0, entropy, bestEntropy = System.Double.MaxValue, currentVal;
			double[] distribution;
			int bestNumBins = 1;
			Instance currentInstance;
			
			// Find minimum and maximum
			for (int i = 0; i < getInputFormat().numInstances(); i++)
			{
				currentInstance = getInputFormat().instance(i);
				if (!currentInstance.isMissing(index))
				{
					currentVal = currentInstance.value_Renamed(index);
					if (currentVal > max)
					{
						max = currentVal;
					}
					if (currentVal < min)
					{
						min = currentVal;
					}
				}
			}
			
			// Find best number of bins
			for (int i = 0; i < m_NumBins; i++)
			{
				distribution = new double[i + 1];
				binWidth = (max - min) / (i + 1);
				
				// Compute distribution
				for (int j = 0; j < getInputFormat().numInstances(); j++)
				{
					currentInstance = getInputFormat().instance(j);
					if (!currentInstance.isMissing(index))
					{
						for (int k = 0; k < i + 1; k++)
						{
							if (currentInstance.value_Renamed(index) <= (min + (((double) k + 1) * binWidth)))
							{
								distribution[k] += currentInstance.weight();
								break;
							}
						}
					}
				}
				
				// Compute cross-validated entropy
				entropy = 0;
				for (int k = 0; k < i + 1; k++)
				{
					if (distribution[k] < 2)
					{
						//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
						entropy = System.Double.MaxValue;
						break;
					}
					entropy -= distribution[k] * System.Math.Log((distribution[k] - 1) / binWidth);
				}
				
				// Best entropy so far?
				if (entropy < bestEntropy)
				{
					bestEntropy = entropy;
					bestNumBins = i + 1;
				}
			}
			
			// Compute cut points
			double[] cutPoints = null;
			if ((bestNumBins > 1) && (binWidth > 0))
			{
				cutPoints = new double[bestNumBins - 1];
				for (int i = 1; i < bestNumBins; i++)
				{
					cutPoints[i - 1] = min + binWidth * i;
				}
			}
			m_CutPoints[index] = cutPoints;
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
				if ((m_DiscretizeCols.isInRange(i)) && (getInputFormat().attribute(i).Numeric) && (getInputFormat().classIndex() != i))
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
				if (m_DiscretizeCols.isInRange(i) && getInputFormat().attribute(i).Numeric && (getInputFormat().classIndex() != i))
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