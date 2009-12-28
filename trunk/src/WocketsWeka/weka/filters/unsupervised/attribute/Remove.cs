/*
*    Remove.java
*    Copyright (C) 1999 Len Trigg
*/
using System;
using Attribute = weka.core.Attribute;
using FastVector = weka.core.FastVector;
using Instance = weka.core.Instance;
using Instances = weka.core.Instances;
using Option = weka.core.Option;
using Range = weka.core.Range;
using SparseInstance = weka.core.SparseInstance;
using Utils = weka.core.Utils;
using Filter = weka.filters.Filter;
using StreamableFilter = weka.filters.StreamableFilter;
using UnsupervisedFilter = weka.filters.UnsupervisedFilter;
namespace weka.filters.unsupervised.attribute
{
	
	/// <summary> An instance filter that deletes a range of attributes from the dataset.<p>
	/// 
	/// Valid filter-specific options are:<p>
	/// 
	/// -R index1,index2-index4,...<br>
	/// Specify list of columns to delete. First and last are valid indexes.
	/// (default none)<p>
	/// 
	/// -V<br>
	/// Invert matching sense (i.e. only keep specified columns)<p>
	/// 
	/// </summary>
	/// <author>  Len Trigg (trigg@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.4.2.1 $
	/// </version>
	/// <attribute>  System.ComponentModel.DescriptionAttribute("An instance filter that deletes a range of attributes from the dataset.")  </attribute>
#if !PocketPC
    [Serializable]
#endif
	public class Remove:Filter, UnsupervisedFilter, StreamableFilter
	{
		/// <summary>Stores which columns to select as a funky range </summary>
		protected internal Range m_SelectCols = new Range();
		/// <summary> Stores the indexes of the selected attributes in order, once the
		/// dataset is seen
		/// </summary>
		protected internal int[] m_SelectedAttributes;
		/// <summary> Contains an index of string attributes in the input format
		/// that will survive the filtering process 
		/// </summary>
		protected internal int[] m_InputStringIndex;
		
		/// <summary> Constructor so that we can initialize the Range variable properly.</summary>
		public Remove()
		{
			
			m_SelectCols.Invert = true;
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
		/// <exception cref="Exception">if the format couldn't be set successfully
		/// </exception>
		public override bool setInputFormat(Instances instanceInfo)
		{
			
			base.setInputFormat(instanceInfo);
			
			m_SelectCols.Upper = instanceInfo.numAttributes() - 1;
			
			// Create the output buffer
			FastVector attributes = new FastVector();
			int outputClass = - 1;
			m_SelectedAttributes = m_SelectCols.Selection;
			int inStrKeepLen = 0;
			int[] inStrKeep = new int[m_SelectedAttributes.Length];
			for (int i = 0; i < m_SelectedAttributes.Length; i++)
			{
				int current = m_SelectedAttributes[i];
				if (instanceInfo.classIndex() == current)
				{
					outputClass = attributes.size();
				}
				Attribute keep = (Attribute) instanceInfo.attribute(current).copy();
				if (keep.type() == Attribute.STRING)
				{
					inStrKeep[inStrKeepLen++] = current;
				}
				attributes.addElement(keep);
			}
			m_InputStringIndex = new int[inStrKeepLen];
			Array.Copy(inStrKeep, 0, m_InputStringIndex, 0, inStrKeepLen);
			Instances outputFormat = new Instances(instanceInfo.relationName(), attributes, 0);
			outputFormat.ClassIndex = outputClass;
			setOutputFormat(outputFormat);
			return true;
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
		/// <exception cref="IllegalStateException">if no input structure has been defined.
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
			
			if (getOutputFormat().numAttributes() == 0)
			{
				return false;
			}
			double[] vals = new double[getOutputFormat().numAttributes()];
			for (int i = 0; i < m_SelectedAttributes.Length; i++)
			{
				int current = m_SelectedAttributes[i];
				vals[i] = instance.value_Renamed(current);
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
			copyStringValues(inst, false, instance.dataset(), m_InputStringIndex, getOutputFormat(), OutputStringIndex);
			inst.Dataset = getOutputFormat();
			push(inst);
			return true;
		}
		
		
		/// <summary> Get whether the supplied columns are to be removed or kept
		/// 
		/// </summary>
		/// <returns> true if the supplied columns will be kept
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Determines whether action is to select or delete. If set to true, only the specified attributes will be kept; If set to false, specified attributes will be deleted.")  </attribute>
		/// <property>   </property>
		public virtual bool get_InvertSelection()
		{
			
			return !m_SelectCols.Invert;
		}
		
		/// <summary> Set whether selected columns should be removed or kept. If true the 
		/// selected columns are kept and unselected columns are deleted. If false
		/// selected columns are deleted and unselected columns are kept.
		/// 
		/// </summary>
		/// <param name="invert">the new invert setting
		/// </param>
		/// <property>   </property>
		public virtual void  set_InvertSelection(bool invert)
		{
			
			m_SelectCols.Invert = !invert;
		}
		
		
		/// <summary> Get the current range selection.
		/// 
		/// </summary>
		/// <returns> a string containing a comma separated list of ranges
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Specify range of attributes to act on. This is a comma separated list of attribute indices, with \"first\" and \"last\" valid values. Specify an inclusive range with \"-\". E.g: \"first-3,5,6-10,last\".")  </attribute>
		/// <property>   </property>
		public virtual System.String get_AttributeIndices()
		{
			
			return m_SelectCols.Ranges;
		}
		
		/// <summary> Set which attributes are to be deleted (or kept if invert is true)
		/// 
		/// </summary>
		/// <param name="rangeList">a string representing the list of attributes.  Since
		/// the string will typically come from a user, attributes are indexed from
		/// 1. <br>
		/// eg: first-3,5,6-last
		/// </param>
		/// <property>   </property>
		public virtual void  set_AttributeIndices(System.String rangeList)
		{
			
			m_SelectCols.Ranges = rangeList;
		}
		
		/// <summary> Set which attributes are to be deleted (or kept if invert is true)
		/// 
		/// </summary>
		/// <param name="attributes">an array containing indexes of attributes to select.
		/// Since the array will typically come from a program, attributes are indexed
		/// from 0.
		/// </param>
		public virtual void  SetAttributeIndicesArray(int[] attributes)
		{
			set_AttributeIndices(Range.indicesToRangeList(attributes));
		}
	}
}