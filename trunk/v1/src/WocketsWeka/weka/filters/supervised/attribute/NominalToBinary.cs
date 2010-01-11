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
*    NominalToBinary.java
*    Copyright (C) 1999 Eibe Frank
*
*/
using System;
using weka.filters;
using weka.core;
namespace weka.filters.supervised.attribute
{
	
	/// <summary> Converts all nominal attributes into binary numeric attributes. An
	/// attribute with k values is transformed into k binary attributes if
	/// the class is nominal (using the one-attribute-per-value approach).
	/// Binary attributes are left binary.
	/// 
	/// If the class is numeric, k - 1 new binary attributes are generated
	/// (in the manner described in "Classification and Regression
	/// Trees").<p>
	/// 
	/// Valid filter-specific options are: <p>
	/// 
	/// -N <br>
	/// If binary attributes are to be coded as nominal ones.<p>
	/// 
	/// -A <br>
	/// For each nominal value a new attribute is created, not only if there are more than 2 values.<p>
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz) 
	/// </author>
	/// <version>  $Revision: 1.3 $ 
	/// </version>
	[Serializable]
	public class NominalToBinary:Filter, SupervisedFilter, OptionHandler
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the current settings of the filter.
		/// 
		/// </summary>
		/// <returns> an array of strings suitable for passing to setOptions
		/// </returns>
		/// <summary> Parses the options for this object. Valid options are: <p>
		/// 
		/// -N <br>
		/// If binary attributes are to be coded as nominal ones.<p>
		/// 
		/// -A <br>
		/// Whether all nominal values are turned into new attributes.<p>
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
				
				System.String[] options = new System.String[1];
				int current = 0;
				
				if (BinaryAttributesNominal)
				{
					options[current++] = "-N";
				}
				
				if (TransformAllValues)
				{
					options[current++] = "-A";
				}
				
				while (current < options.Length)
				{
					options[current++] = "";
				}
				return options;
			}
			
			set
			{
				
				BinaryAttributesNominal = Utils.getFlag('N', value);
				
				TransformAllValues = Utils.getFlag('A', value);
				
				if (getInputFormat() != null)
					setInputFormat(getInputFormat());
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets if binary attributes are to be treated as nominal ones.
		/// 
		/// </summary>
		/// <returns> true if binary attributes are to be treated as nominal ones
		/// </returns>
		/// <summary> Sets if binary attributes are to be treates as nominal ones.
		/// 
		/// </summary>
		/// <param name="bool">true if binary attributes are to be treated as nominal ones
		/// </param>
		virtual public bool BinaryAttributesNominal
		{
			get
			{
				
				return !m_Numeric;
			}
			
			set
			{
				
				m_Numeric = !value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets if all nominal values are turned into new attributes, not only if
		/// there are more than 2.
		/// 
		/// </summary>
		/// <returns> true all nominal values are transformed into new attributes
		/// </returns>
		/// <summary> Sets whether all nominal values are transformed into new attributes, not
		/// just if there are more than 2.
		/// 
		/// </summary>
		/// <param name="bool">true if all nominal value are transformed into new attributes
		/// </param>
		virtual public bool TransformAllValues
		{
			get
			{
				
				return m_TransformAll;
			}
			
			set
			{
				
				m_TransformAll = value;
			}
			
		}
		
		/// <summary>The sorted indices of the attribute values. </summary>
		private int[][] m_Indices = null;
		
		/// <summary>Are the new attributes going to be nominal or numeric ones? </summary>
		private bool m_Numeric = true;
		
		/// <summary>Are all values transformed into new attributes? </summary>
		private bool m_TransformAll = false;
		
		/// <summary> Returns a string describing this filter
		/// 
		/// </summary>
		/// <returns> a description of the filter suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String globalInfo()
		{
			
			return "Converts all nominal attributes into binary numeric attributes. An " + "attribute with k values is transformed into k binary attributes if " + "the class is nominal (using the one-attribute-per-value approach). " + "Binary attributes are left binary, if option '-A' is not given." + "If the class is numeric, k - 1 new binary attributes are generated " + "in the manner described in \"Classification and Regression " + "Trees\" by Breiman et al. (i.e. taking the average class value associated " + "with each attribute value into account)";
		}
		
		/// <summary> Sets the format of the input instances.
		/// 
		/// </summary>
		/// <param name="instanceInfo">an Instances object containing the input 
		/// instance structure (any instances contained in the object are 
		/// ignored - only the structure is required).
		/// </param>
		/// <returns> true if the outputFormat may be collected immediately
		/// </returns>
		/// <exception cref="Exception">if the input format can't be set 
		/// successfully
		/// </exception>
		public override bool setInputFormat(Instances instanceInfo)
		{
			
			base.setInputFormat(instanceInfo);
			if (instanceInfo.classIndex() < 0)
			{
				throw new Exception("No class has been assigned to the instances");
			}
			setOutputFormat();
			m_Indices = null;
			if (instanceInfo.classAttribute().Nominal)
			{
				return true;
			}
			else
			{
				return false;
			}
		}
		
		/// <summary> Input an instance for filtering. Filter requires all
		/// training instances be read before producing output.
		/// 
		/// </summary>
		/// <param name="instance">the input instance
		/// </param>
		/// <returns> true if the filtered instance may now be
		/// collected with output().
		/// </returns>
		/// <exception cref="IllegalStateException">if no input format has been set
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
			if ((m_Indices != null) || (getInputFormat().classAttribute().Nominal))
			{
				convertInstance(instance);
				return true;
			}
			bufferInput(instance);
			return false;
		}
		
		/// <summary> Signify that this batch of input to the filter is finished. 
		/// If the filter requires all instances prior to filtering,
		/// output() may now be called to retrieve the filtered instances.
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
			if ((m_Indices == null) && (getInputFormat().classAttribute().Numeric))
			{
				computeAverageClassValues();
				setOutputFormat();
				
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
		
		/// <summary> Returns an enumeration describing the available options.
		/// 
		/// </summary>
		/// <returns> an enumeration of all the available options.
		/// </returns>
		public virtual System.Collections.IEnumerator listOptions()
		{
			
			System.Collections.ArrayList newVector = System.Collections.ArrayList.Synchronized(new System.Collections.ArrayList(1));
			
			newVector.Add(new Option("\tSets if binary attributes are to be coded as nominal ones.", "N", 0, "-N"));
			newVector.Add(new Option("\tFor each nominal value a new attribute is created, \nnot only if there are more than 2 values.", "A", 0, "-A"));
			
			return newVector.GetEnumerator();
		}
		
		/// <summary> Returns the tip text for this property
		/// 
		/// </summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String binaryAttributesNominalTipText()
		{
			return "Whether resulting binary attributes will be nominal.";
		}
		
		/// <summary> Returns the tip text for this property
		/// 
		/// </summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String transformAllValuesTipText()
		{
			return "Whether all nominal values are turned into new attributes, not only if there are more than 2.";
		}
		
		/// <summary>Computes average class values for each attribute and value </summary>
		private void  computeAverageClassValues()
		{
			
			double totalCounts, sum;
			Instance instance;
			double[] counts;
			
			double[][] avgClassValues = new double[getInputFormat().numAttributes()][];
			for (int i = 0; i < getInputFormat().numAttributes(); i++)
			{
				avgClassValues[i] = new double[0];
			}
			m_Indices = new int[getInputFormat().numAttributes()][];
			for (int i2 = 0; i2 < getInputFormat().numAttributes(); i2++)
			{
				m_Indices[i2] = new int[0];
			}
			for (int j = 0; j < getInputFormat().numAttributes(); j++)
			{
                weka.core.Attribute att = getInputFormat().attribute(j);
				if (att.Nominal)
				{
					avgClassValues[j] = new double[att.numValues()];
					counts = new double[att.numValues()];
					for (int i = 0; i < getInputFormat().numInstances(); i++)
					{
						instance = getInputFormat().instance(i);
						if (!instance.classIsMissing() && (!instance.isMissing(j)))
						{
							//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
							counts[(int) instance.value_Renamed(j)] += instance.weight();
							//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
							avgClassValues[j][(int) instance.value_Renamed(j)] += instance.weight() * instance.classValue();
						}
					}
					sum = Utils.sum(avgClassValues[j]);
					totalCounts = Utils.sum(counts);
					if (Utils.gr(totalCounts, 0))
					{
						for (int k = 0; k < att.numValues(); k++)
						{
							if (Utils.gr(counts[k], 0))
							{
								avgClassValues[j][k] /= (double) counts[k];
							}
							else
							{
								avgClassValues[j][k] = sum / (double) totalCounts;
							}
						}
					}
					m_Indices[j] = Utils.sort(avgClassValues[j]);
				}
			}
		}
		
		/// <summary>Set the output format. </summary>
		private void  setOutputFormat()
		{
			
			if (getInputFormat().classAttribute().Nominal)
			{
				setOutputFormatNominal();
			}
			else
			{
				setOutputFormatNumeric();
			}
		}
		
		/// <summary> Convert a single instance over. The converted instance is 
		/// added to the end of the output queue.
		/// 
		/// </summary>
		/// <param name="instance">the instance to convert
		/// </param>
		private void  convertInstance(Instance inst)
		{
			
			if (getInputFormat().classAttribute().Nominal)
			{
				convertInstanceNominal(inst);
			}
			else
			{
				convertInstanceNumeric(inst);
			}
		}
		
		/// <summary> Set the output format if the class is nominal.</summary>
		private void  setOutputFormatNominal()
		{
			
			FastVector newAtts;
			int newClassIndex;
			System.Text.StringBuilder attributeName;
			Instances outputFormat;
			FastVector vals;
			
			// Compute new attributes
			
			newClassIndex = getInputFormat().classIndex();
			newAtts = new FastVector();
			for (int j = 0; j < getInputFormat().numAttributes(); j++)
			{
                weka.core.Attribute att = getInputFormat().attribute(j);
				if ((!att.Nominal) || (j == getInputFormat().classIndex()))
				{
					newAtts.addElement(att.copy());
				}
				else
				{
					if ((att.numValues() <= 2) && (!m_TransformAll))
					{
						if (m_Numeric)
						{
                            newAtts.addElement(new weka.core.Attribute(att.name()));
						}
						else
						{
							newAtts.addElement(att.copy());
						}
					}
					else
					{
						
						if (j < getInputFormat().classIndex())
						{
							newClassIndex += att.numValues() - 1;
						}
						
						// Compute values for new attributes
						for (int k = 0; k < att.numValues(); k++)
						{
							attributeName = new System.Text.StringBuilder(att.name() + "=");
							attributeName.Append(att.value_Renamed(k));
							if (m_Numeric)
							{
                                newAtts.addElement(new weka.core.Attribute(attributeName.ToString()));
							}
							else
							{
								vals = new FastVector(2);
								vals.addElement("f"); vals.addElement("t");
                                newAtts.addElement(new weka.core.Attribute(attributeName.ToString(), vals));
							}
						}
					}
				}
			}
			outputFormat = new Instances(getInputFormat().relationName(), newAtts, 0);
			outputFormat.ClassIndex = newClassIndex;
			setOutputFormat(outputFormat);
		}
		
		/// <summary> Set the output format if the class is numeric.</summary>
		private void  setOutputFormatNumeric()
		{
			
			if (m_Indices == null)
			{
				setOutputFormat(null);
				return ;
			}
			FastVector newAtts;
			int newClassIndex;
			System.Text.StringBuilder attributeName;
			Instances outputFormat;
			FastVector vals;
			
			// Compute new attributes
			
			newClassIndex = getInputFormat().classIndex();
			newAtts = new FastVector();
			for (int j = 0; j < getInputFormat().numAttributes(); j++)
			{
                weka.core.Attribute att = getInputFormat().attribute(j);
				if ((!att.Nominal) || (j == getInputFormat().classIndex()))
				{
					newAtts.addElement(att.copy());
				}
				else
				{
					if (j < getInputFormat().classIndex())
						newClassIndex += att.numValues() - 2;
					
					// Compute values for new attributes
					
					for (int k = 1; k < att.numValues(); k++)
					{
						attributeName = new System.Text.StringBuilder(att.name() + "=");
						for (int l = k; l < att.numValues(); l++)
						{
							if (l > k)
							{
								attributeName.Append(',');
							}
							attributeName.Append(att.value_Renamed(m_Indices[j][l]));
						}
						if (m_Numeric)
						{
                            newAtts.addElement(new weka.core.Attribute(attributeName.ToString()));
						}
						else
						{
							vals = new FastVector(2);
							vals.addElement("f"); vals.addElement("t");
                            newAtts.addElement(new weka.core.Attribute(attributeName.ToString(), vals));
						}
					}
				}
			}
			outputFormat = new Instances(getInputFormat().relationName(), newAtts, 0);
			outputFormat.ClassIndex = newClassIndex;
			setOutputFormat(outputFormat);
		}
		
		/// <summary> Convert a single instance over if the class is nominal. The converted 
		/// instance is added to the end of the output queue.
		/// 
		/// </summary>
		/// <param name="instance">the instance to convert
		/// </param>
		private void  convertInstanceNominal(Instance instance)
		{
			
			double[] vals = new double[outputFormatPeek().numAttributes()];
			int attSoFar = 0;
			
			for (int j = 0; j < getInputFormat().numAttributes(); j++)
			{
                weka.core.Attribute att = getInputFormat().attribute(j);
				if ((!att.Nominal) || (j == getInputFormat().classIndex()))
				{
					vals[attSoFar] = instance.value_Renamed(j);
					attSoFar++;
				}
				else
				{
					if ((att.numValues() <= 2) && (!m_TransformAll))
					{
						vals[attSoFar] = instance.value_Renamed(j);
						attSoFar++;
					}
					else
					{
						if (instance.isMissing(j))
						{
							for (int k = 0; k < att.numValues(); k++)
							{
								vals[attSoFar + k] = instance.value_Renamed(j);
							}
						}
						else
						{
							for (int k = 0; k < att.numValues(); k++)
							{
								//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
								if (k == (int) instance.value_Renamed(j))
								{
									vals[attSoFar + k] = 1;
								}
								else
								{
									vals[attSoFar + k] = 0;
								}
							}
						}
						attSoFar += att.numValues();
					}
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
		
		/// <summary> Convert a single instance over if the class is numeric. The converted 
		/// instance is added to the end of the output queue.
		/// 
		/// </summary>
		/// <param name="instance">the instance to convert
		/// </param>
		private void  convertInstanceNumeric(Instance instance)
		{
			
			double[] vals = new double[outputFormatPeek().numAttributes()];
			int attSoFar = 0;
			
			for (int j = 0; j < getInputFormat().numAttributes(); j++)
			{
                weka.core.Attribute att = getInputFormat().attribute(j);
				if ((!att.Nominal) || (j == getInputFormat().classIndex()))
				{
					vals[attSoFar] = instance.value_Renamed(j);
					attSoFar++;
				}
				else
				{
					if (instance.isMissing(j))
					{
						for (int k = 0; k < att.numValues() - 1; k++)
						{
							vals[attSoFar + k] = instance.value_Renamed(j);
						}
					}
					else
					{
						int k = 0;
						//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
						while ((int) instance.value_Renamed(j) != m_Indices[j][k])
						{
							vals[attSoFar + k] = 1;
							k++;
						}
						while (k < att.numValues() - 1)
						{
							vals[attSoFar + k] = 0;
							k++;
						}
					}
					attSoFar += att.numValues() - 1;
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