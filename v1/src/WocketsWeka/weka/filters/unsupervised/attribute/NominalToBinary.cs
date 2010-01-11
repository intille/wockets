/*
*    NominalToBinary.java
*    Copyright (C) 1999 Eibe Frank
*/
using System;
using weka.filters;
using weka.core;
namespace weka.filters.unsupervised.attribute
{
	
	/// <summary> Converts all nominal attributes into binary numeric attributes. An
	/// attribute with k values is transformed into k binary attributes
	/// (using the one-attribute-per-value approach).
	/// Binary attributes are left binary.
	/// 
	/// Valid filter-specific options are: <p>
	/// 
	/// -N <br>
	/// If binary attributes are to be coded as nominal ones.<p>
	/// 
	/// -R col1,col2-col4,... <br>
	/// Specifies list of columns to convert. First
	/// and last are valid indexes. (default: first-last) <p>
	/// 
	/// -V <br>
	/// Invert matching sense.<p>
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz) 
	/// </author>
	/// <version>  $Revision: 1.6 $ 
	/// </version>
	/// <attribute>  System.ComponentModel.DescriptionAttribute("Converts all nominal attributes into binary numeric attributes.")  </attribute>
    /// 
#if !PocketPC
	[Serializable]
#endif
	public class NominalToBinary:Filter, UnsupervisedFilter
	//,OptionHandler 
	{
		/// <summary>Stores which columns to act on </summary>
		protected internal Range m_Columns = new Range();
		/// <summary>The sorted indices of the attribute values. </summary>
		private int[][] m_Indices = null;
		/// <summary>Are the new attributes going to be nominal or numeric ones? </summary>
		private bool m_Numeric = true;
		
		/// <summary>Constructor - initialises the filter </summary>
		public NominalToBinary()
		{
			set_AttributeIndices("first-last");
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
			
			m_Columns.Upper = instanceInfo.numAttributes() - 1;
			
			setOutputFormat();
			m_Indices = null;
			return true;
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
			
			convertInstance(instance);
			return true;
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
		
		/// <summary> Gets if binary attributes are to be treated as nominal ones.
		/// 
		/// </summary>
		/// <returns> true if binary attributes are to be treated as nominal ones
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Whether resulting binary attributes will be nominal.")  </attribute>
		/// <property>   </property>
		public virtual bool get_BinaryAttributesNominal()
		{
			
			return !m_Numeric;
		}
		
		/// <summary> Sets if binary attributes are to be treates as nominal ones.
		/// 
		/// </summary>
		/// <param name="bool">true if binary attributes are to be treated as nominal ones
		/// </param>
		/// <property>   </property>
		public virtual void  set_BinaryAttributesNominal(bool bool_Renamed)
		{
			
			m_Numeric = !bool_Renamed;
		}
		
		
		/// <summary> Gets whether the supplied columns are to be removed or kept
		/// 
		/// </summary>
		/// <returns> true if the supplied columns will be kept
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Set attribute selection mode. If false, only selected (numeric) attributes in the range will be discretized; if true, only non-selected attributes will be discretized.")  </attribute>
		/// <property>   </property>
		public virtual bool get_InvertSelection()
		{
			
			return m_Columns.Invert;
		}
		
		/// <summary> Sets whether selected columns should be removed or kept. If true the 
		/// selected columns are kept and unselected columns are deleted. If false
		/// selected columns are deleted and unselected columns are kept.
		/// 
		/// </summary>
		/// <param name="invert">the new invert setting
		/// </param>
		/// <property>   </property>
		public virtual void  set_InvertSelection(bool invert)
		{
			
			m_Columns.Invert = invert;
		}
		
		
		/// <summary> Gets the current range selection
		/// 
		/// </summary>
		/// <returns> a string containing a comma separated list of ranges
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Specify range of attributes to act on. This is a comma separated list of attribute indices, with \"first\" and \"last\" valid values. Specify an inclusive range with \"-\". E.g: \"first-3,5,6-10,last\".")  </attribute>
		/// <property>   </property>
		public virtual System.String get_AttributeIndices()
		{
			
			return m_Columns.Ranges;
		}
		
		/// <summary> Sets which attributes are to be acted on.
		/// 
		/// </summary>
		/// <param name="rangeList">a string representing the list of attributes. Since
		/// the string will typically come from a user, attributes are indexed from
		/// 1. <br>
		/// eg: first-3,5,6-last
		/// </param>
		/// <exception cref="IllegalArgumentException">if an invalid range list is supplied 
		/// </exception>
		/// <property>   </property>
		public virtual void  set_AttributeIndices(System.String rangeList)
		{
			
			m_Columns.Ranges = rangeList;
		}
		
		/// <summary> Set the output format if the class is nominal.</summary>
		private void  setOutputFormat()
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
				if (!att.Nominal || (j == getInputFormat().classIndex()) || !m_Columns.isInRange(j))
				{
					newAtts.addElement(att.copy());
				}
				else
				{
					if (att.numValues() <= 2)
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
						
						if (newClassIndex >= 0 && j < getInputFormat().classIndex())
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
		
		/// <summary> Convert a single instance over if the class is nominal. The converted 
		/// instance is added to the end of the output queue.
		/// 
		/// </summary>
		/// <param name="instance">the instance to convert
		/// </param>
		private void  convertInstance(Instance instance)
		{
			
			double[] vals = new double[outputFormatPeek().numAttributes()];
			int attSoFar = 0;
			
			for (int j = 0; j < getInputFormat().numAttributes(); j++)
			{
                weka.core.Attribute att = getInputFormat().attribute(j);
				if (!att.Nominal || (j == getInputFormat().classIndex()) || !m_Columns.isInRange(j))
				{
					vals[attSoFar] = instance.value_Renamed(j);
					attSoFar++;
				}
				else
				{
					if (att.numValues() <= 2)
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
	}
}