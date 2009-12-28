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
*    ClassOrder.java
*    Copyright (C) 2002 Xin Xu
*
*/
using System;
using weka.filters;
using Attribute = weka.core.Attribute;
using Instance = weka.core.Instance;
using Instances = weka.core.Instances;
using Option = weka.core.Option;
using OptionHandler = weka.core.OptionHandler;
using Utils = weka.core.Utils;
using FastVector = weka.core.FastVector;
namespace weka.filters.supervised.attribute
{
	
	/// <summary> A filter that sorts the order of classes so that the class values are 
	/// no longer of in the order of that in the header file after filtered.
	/// The values of the class will be in the order specified by the user
	/// -- it could be either in ascending/descending order by the class
	/// frequency or in random order.<p>
	/// 
	/// The format of the header is thus not changed in this filter 
	/// (although it still uses <code>setInputFormat()</code>), but
	/// the class value of each instance is converted to sorted 
	/// values within the same range.  The value can also be converted back
	/// using <code>originalValue(double value)</code> procedure.<p>  
	/// 
	/// </summary>
	/// <author>  Xin Xu (xx5@cs.waikato.ac.nz)
	/// </author>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.4 $
	/// </version>
	[Serializable]
	public class ClassOrder:Filter, SupervisedFilter, OptionHandler
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the current settings of the filter.
		/// 
		/// </summary>
		/// <returns> an array of strings suitable for passing to setOptions
		/// </returns>
		/// <summary> Parses a given list of options controlling the behaviour of this object.
		/// Valid options are:<p>
		/// 
		/// -R <seed> <br>
		/// Specify the seed of randomization used to randomize the class order
		/// (default: 1)<p>
		/// 
		/// -C <order><br>
		/// Specify the class order to be sorted, could be 0: ascending, 1: descending 
		/// and 2: random(default: 0)<p>
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
				
				System.String[] options = new System.String[4];
				int current = 0;
				
				options[current++] = "-R";
				options[current++] = "" + m_Seed;
				options[current++] = "-C";
				options[current++] = "" + m_ClassOrder;
				
				while (current < options.Length)
				{
					options[current++] = "";
				}
				return options;
			}
			
			set
			{
				
				System.String seedString = Utils.getOption('R', value);
				if (seedString.Length != 0)
					m_Seed = System.Int64.Parse(seedString);
				else
					m_Seed = 1;
				
				System.String orderString = Utils.getOption('C', value);
				if (orderString.Length != 0)
					m_ClassOrder = System.Int32.Parse(orderString);
				else
					m_ClassOrder = FREQ_ASCEND;
				
				if (getInputFormat() != null)
					setInputFormat(getInputFormat());
				
				m_Random = null;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Get the current randomization seed
		/// 
		/// </summary>
		/// <returns> a seed
		/// </returns>
		/// <summary> Set randomization seed
		/// 
		/// </summary>
		/// <param name="seed">the set seed
		/// </param>
		virtual public long Seed
		{
			get
			{
				return m_Seed;
			}
			
			set
			{
				m_Seed = value;
				m_Random = null;
			}
			
		}
		/// <summary> Get the class distribution of the sorted class values.  If class is numeric
		/// it returns null 
		/// 
		/// </summary>
		/// <returns> the class counts
		/// </returns>
		virtual public double[] ClassCounts
		{
			get
			{
				
				if (m_ClassAttribute.Nominal)
					return m_ClassCounts;
				else
					return null;
			}
			
		}
		
		/// <summary>The seed of randomization </summary>
		private long m_Seed = 1;
		
		/// <summary>The random object </summary>
		private System.Random m_Random = null;
		
		/// <summary> The 1-1 converting table from the original class values
		/// to the new values
		/// </summary>
		private int[] m_Converter = null;
		
		/// <summary>Class attribute of the data </summary>
		private Attribute m_ClassAttribute = null;
		
		/// <summary>The class order to be sorted </summary>
		private int m_ClassOrder = 0;
		
		/// <summary>The class values are sorted in ascending order based on their frequencies </summary>
		public const int FREQ_ASCEND = 0;
		
		/// <summary>The class values are sorted in descending order based on their frequencies </summary>
		public const int FREQ_DESCEND = 1;
		
		/// <summary>The class values are sorted in random order</summary>
		public const int RANDOM = 2;
		
		/// <summary>This class can provide the class distribution in the sorted order 
		/// as side effect 
		/// </summary>
		private double[] m_ClassCounts = null;
		
		/// <summary> Returns a string describing this filter
		/// 
		/// </summary>
		/// <returns> a description of the filter suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String globalInfo()
		{
			
			return "Changes the order of the classes so that the class values are " + "no longer of in the order specified in the header. " + "The values will be in the order specified by the user " + "-- it could be either in ascending/descending order by the class " + "frequency or in random order. Note that this filter currently does not " + "change the header, only the class values of the instances, " + "so there is not much point in using it in conjunction with the " + "FilteredClassifier.";
		}
		
		/// <summary> Returns an enumeration describing the available options.
		/// 
		/// </summary>
		/// <returns> an enumeration of all the available options.
		/// </returns>
		public virtual System.Collections.IEnumerator listOptions()
		{
			
			System.Collections.ArrayList newVector = System.Collections.ArrayList.Synchronized(new System.Collections.ArrayList(1));
			
			newVector.Add(new Option("\tSpecify the seed of randomization\n" + "\tused to randomize the class\n" + "\torder (default: 1)", "R", 1, "-R <seed>"));
			
			newVector.Add(new Option("\tSpecify the class order to be\n" + "\tsorted, could be 0: ascending\n" + "\t1: descending and 2: random.(default: 0)", "C", 1, "-C <order>"));
			
			return newVector.GetEnumerator();
		}
		
		/// <summary> Returns the tip text for this property
		/// 
		/// </summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String seedTipText()
		{
			return "Specify the seed of randomization of the class order";
		}
		
		/// <summary> Returns the tip text for this property
		/// 
		/// </summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String classOrderTipText()
		{
			return "Specify the class order after the filtering";
		}
		
		/// <summary> Get the wanted class order
		/// 
		/// </summary>
		/// <returns> class order
		/// </returns>
		public virtual int getClassOrder()
		{
			return m_ClassOrder;
		}
		
		/// <summary> Set the wanted class order
		/// 
		/// </summary>
		/// <param name="order">the class order
		/// </param>
		public virtual void  setClassOrder(int order)
		{
			m_ClassOrder = order;
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
		public override bool setInputFormat(Instances instanceInfo)
		{
			
			base.setInputFormat(new Instances(instanceInfo, 0));
			if (instanceInfo.classIndex() < 0)
			{
				throw new System.ArgumentException("ClassOrder: No class index set.");
			}
			if (!instanceInfo.classAttribute().Nominal)
			{
				throw new System.ArgumentException("ClassOrder: Class must be nominal.");
			}
			m_ClassAttribute = instanceInfo.classAttribute();
			//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.util.Random.Random'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
			m_Random = new System.Random((System.Int32) m_Seed);
			m_Converter = null;
			
			int numClasses = instanceInfo.numClasses();
			m_ClassCounts = new double[numClasses];
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
			
			// In case some one use this routine in testing, 
			// although he/she should not do so
			if (m_Converter != null)
			{
				Instance datum = (Instance) instance.copy();
				if (!datum.isMissing(m_ClassAttribute))
				{
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					datum.setClassValue((double) m_Converter[(int) datum.classValue()]);
				}
				push(datum);
				return true;
			}
			
			if (!instance.isMissing(m_ClassAttribute))
			{
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				m_ClassCounts[(int) instance.classValue()] += instance.weight();
			}
			
			bufferInput(instance);
			return false;
		}
		
		/// <summary> Signify that this batch of input to the filter is finished. If
		/// the filter requires all instances prior to filtering, output()
		/// may now be called to retrieve the filtered instances. Any
		/// subsequent instances filtered should be filtered based on setting
		/// obtained from the first batch (unless the inputFormat has been
		/// re-assigned or new options have been set). This implementation 
		/// sorts the class values and provide class counts in the output format
		/// 
		/// </summary>
		/// <returns> true if there are instances pending output
		/// </returns>
		/// <exception cref="NullPointerException">if no input structure has been defined,
		/// </exception>
		/// <exception cref="Exception">if there was a problem finishing the batch.
		/// </exception>
		public override bool batchFinished()
		{
			
			Instances data = getInputFormat();
			if (data == null)
				throw new System.SystemException("No input instance format defined");
			
			if (m_Converter == null)
			{
				
				// Get randomized indices and class counts 
				int[] randomIndices = new int[m_ClassCounts.Length];
				for (int i = 0; i < randomIndices.Length; i++)
				{
					randomIndices[i] = i;
				}
				for (int j = randomIndices.Length - 1; j > 0; j--)
				{
					int toSwap = m_Random.Next(j + 1);
					int tmpIndex = randomIndices[j];
					randomIndices[j] = randomIndices[toSwap];
					randomIndices[toSwap] = tmpIndex;
				}
				
				double[] randomizedCounts = new double[m_ClassCounts.Length];
				for (int i = 0; i < randomizedCounts.Length; i++)
				{
					randomizedCounts[i] = m_ClassCounts[randomIndices[i]];
				}
				
				// Create new order. For the moment m_Converter converts new indices
				// into old ones.
				if (m_ClassOrder == RANDOM)
				{
					m_Converter = randomIndices;
					m_ClassCounts = randomizedCounts;
				}
				else
				{
					int[] sorted = Utils.sort(randomizedCounts);
					m_Converter = new int[sorted.Length];
					if (m_ClassOrder == FREQ_ASCEND)
					{
						for (int i = 0; i < sorted.Length; i++)
						{
							m_Converter[i] = randomIndices[sorted[i]];
						}
					}
					else if (m_ClassOrder == FREQ_DESCEND)
					{
						for (int i = 0; i < sorted.Length; i++)
						{
							m_Converter[i] = randomIndices[sorted[sorted.Length - i - 1]];
						}
					}
					else
					{
						throw new System.ArgumentException("Class order not defined!");
					}
					
					// Change class counts
					double[] tmp2 = new double[m_ClassCounts.Length];
					for (int i = 0; i < m_Converter.Length; i++)
					{
						tmp2[i] = m_ClassCounts[m_Converter[i]];
					}
					m_ClassCounts = tmp2;
				}
				
				// Change the class values
				FastVector values = new FastVector(data.classAttribute().numValues());
				for (int i = 0; i < data.numClasses(); i++)
				{
					values.addElement(data.classAttribute().value_Renamed(m_Converter[i]));
				}
				FastVector newVec = new FastVector(data.numAttributes());
				for (int i = 0; i < data.numAttributes(); i++)
				{
					if (i == data.classIndex())
					{
						newVec.addElement(new Attribute(data.classAttribute().name(), values, data.classAttribute().getMetadata()));
					}
					else
					{
						newVec.addElement(data.attribute(i));
					}
				}
				Instances newInsts = new Instances(data.relationName(), newVec, 0);
				newInsts.ClassIndex = data.classIndex();
				setOutputFormat(newInsts);
				
				// From now on we need m_Converter to convert old indices into new ones
				int[] temp = new int[m_Converter.Length];
				for (int i = 0; i < temp.Length; i++)
				{
					temp[m_Converter[i]] = i;
				}
				m_Converter = temp;
				
				// Process all instances
				for (int xyz = 0; xyz < data.numInstances(); xyz++)
				{
					Instance datum = data.instance(xyz);
					if (!datum.isMissing(datum.classIndex()))
					{
						//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
						datum.setClassValue((double) m_Converter[(int) datum.classValue()]);
					}
					push(datum);
				}
			}
			flushInput();
			m_NewBatch = true;
			return (numPendingOutput() != 0);
		}
		
		/// <summary> Convert the given class distribution back to the distributions
		/// with the original internal class index
		/// 
		/// </summary>
		/// <param name="before">the given class distribution
		/// </param>
		/// <returns> the distribution converted back
		/// </returns>
		public virtual double[] distributionsByOriginalIndex(double[] before)
		{
			
			double[] after = new double[m_Converter.Length];
			for (int i = 0; i < m_Converter.Length; i++)
				after[i] = before[m_Converter[i]];
			
			return after;
		}
		
		/// <summary> Return the original internal class value given the randomized 
		/// class value, i.e. the string presentations of the two indices
		/// are the same.  It's useful when the filter is used within a classifier  
		/// so that the filtering procedure should be transparent to the 
		/// evaluation
		/// 
		/// </summary>
		/// <param name="value">the given value
		/// </param>
		/// <returns> the original internal value, -1 if not found
		/// </returns>
		/// <exception cref="if">the coverter table is not set yet
		/// </exception>
		public virtual double originalValue(double value_Renamed)
		{
			
			if (m_Converter == null)
				throw new System.SystemException("Coverter table not defined yet!");
			
			for (int i = 0; i < m_Converter.Length; i++)
			{
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				if ((int) value_Renamed == m_Converter[i])
					return (double) i;
			}
			
			return - 1;
		}
		

	}
}