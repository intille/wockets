/*
*    RemoveWithValues.java
*    Copyright (C) 1999 Eibe Frank
*/
using System;
using weka.filters;
using Attribute = weka.core.Attribute;
using FastVector = weka.core.FastVector;
using Instance = weka.core.Instance;
using Instances = weka.core.Instances;
using Option = weka.core.Option;
//UPGRADE_TODO: The type 'weka.core.Range' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using Range = weka.core.Range;
using SparseInstance = weka.core.SparseInstance;
using Utils = weka.core.Utils;
//UPGRADE_TODO: The type 'weka.core.UnsupportedAttributeTypeException' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
//using UnsupportedAttributeTypeException = weka.core.UnsupportedAttributeTypeException;
//UPGRADE_TODO: The type 'weka.core.SingleIndex' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using SingleIndex = weka.core.SingleIndex;
namespace weka.filters.unsupervised.instance
{
	
	/// <summary> Filters instances according to the value of an attribute.<p>
	/// 
	/// Valid filter-specific options are:<p>
	/// 
	/// -C num<br>
	/// Choose attribute to be used for selection (default last).<p>
	/// 
	/// -S num<br>
	/// Numeric value to be used for selection on numeric attribute.
	/// Instances with values smaller than given value will be selected.
	/// (default 0) <p>
	/// 
	/// -L index1,index2-index4,...<br>
	/// Range of label indices to be used for selection on nominal attribute.
	/// First and last are valid indexes. (default all values)<p>
	/// 
	/// -M <br>
	/// Missing values count as a match. This setting is independent of
	/// the -V option. (default missing values don't match)<p>
	/// 
	/// -V<br>
	/// Invert matching sense.<p>
	/// 
	/// -H<br>
	/// When selecting on nominal attributes, removes header references to
	/// excluded values. <p>
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.7.2.1 $
	/// </version>
	/// <attribute>  System.ComponentModel.DescriptionAttribute("Filters instances according to the value of an attribute.")  </attribute>
#if !PocketPC
    [Serializable]
#endif
	public class RemoveWithValues:Filter, UnsupervisedFilter, StreamableFilter
	{
		/// <summary> Returns true if selection attribute is nominal.
		/// 
		/// </summary>
		/// <returns> true if selection attribute is nominal
		/// </returns>
		virtual public bool Nominal
		{
			get
			{
				
				if (getInputFormat() == null)
				{
					return false;
				}
				else
				{
					return getInputFormat().attribute(m_AttIndex.Index).Nominal;
				}
			}
			
		}
		/// <summary> Returns true if selection attribute is numeric.
		/// 
		/// </summary>
		/// <returns> true if selection attribute is numeric
		/// </returns>
		virtual public bool Numeric
		{
			get
			{
				
				if (getInputFormat() == null)
				{
					return false;
				}
				else
				{
					return getInputFormat().attribute(m_AttIndex.Index).Numeric;
				}
			}
			
		}
		/// <summary> Set which values of a nominal attribute are to be used for
		/// selection.
		/// 
		/// </summary>
		/// <param name="values">an array containing indexes of values to be
		/// used for selection
		/// </param>
		/// <exception cref="InvalidArgumentException">if an invalid set of ranges is supplied
		/// </exception>
		virtual public int[] NominalIndicesArr
		{
			set
			{
				System.String rangeList = "";
				for (int i = 0; i < value.Length; i++)
				{
					if (i == 0)
					{
						rangeList = "" + (value[i] + 1);
					}
					else
					{
						rangeList += ("," + (value[i] + 1));
					}
				}
				set_NominalIndices(rangeList);
			}
			
		}
		/// <summary>The attribute's index setting. </summary>
		private SingleIndex m_AttIndex = new SingleIndex("last");
		/// <summary>Stores which values of nominal attribute are to be used for filtering.</summary>
		protected internal Range m_Values;
		/// <summary>Stores which value of a numeric attribute is to be used for filtering.</summary>
		protected internal double m_Value = 0;
		/// <summary>True if missing values should count as a match </summary>
		protected internal bool m_MatchMissingValues = false;
		/// <summary>Modify header for nominal attributes? </summary>
		protected internal bool m_ModifyHeader = false;
		/// <summary>If m_ModifyHeader, stores a mapping from old to new indexes </summary>
		protected internal int[] m_NominalMapping;
		
		/// <summary>Default constructor </summary>
		public RemoveWithValues()
		{
			
			m_Values = new Range("first-last");
			m_Values.Invert=true;
		}
		
		
		/// <summary> Sets the format of the input instances.
		/// 
		/// </summary>
		/// <param name="instanceInfo">an Instances object containing the input instance
		/// structure (any instances contained in the object are ignored - only the
		/// structure is required).
		/// </param>
		/// <exception cref="UnsupportedAttributeTypeException">if the specified attribute
		/// is neither numeric or nominal.
		/// </exception>
		public override bool setInputFormat(Instances instanceInfo)
		{
			
			base.setInputFormat(instanceInfo);
			
			m_AttIndex.Upper=instanceInfo.numAttributes() - 1;
			if (!Numeric && !Nominal)
			{
				throw new Exception("Can only handle numeric " + "or nominal attributes.");
			}
			m_Values.Upper=instanceInfo.attribute(m_AttIndex.Index).numValues() - 1;
			if (Nominal && m_ModifyHeader)
			{
				instanceInfo = new Instances(instanceInfo, 0); // copy before modifying
				Attribute oldAtt = instanceInfo.attribute(m_AttIndex.Index);
				int[] selection = m_Values.Selection;
				FastVector newVals = new FastVector();
				for (int i = 0; i < selection.Length; i++)
				{
					newVals.addElement(oldAtt.value_Renamed(selection[i]));
				}
				instanceInfo.deleteAttributeAt(m_AttIndex.Index);
				instanceInfo.insertAttributeAt(new Attribute(oldAtt.name(), newVals), m_AttIndex.Index);
				m_NominalMapping = new int[oldAtt.numValues()];
				for (int i = 0; i < m_NominalMapping.Length; i++)
				{
					bool found = false;
					for (int j = 0; j < selection.Length; j++)
					{
						if (selection[j] == i)
						{
							m_NominalMapping[i] = j;
							found = true;
							break;
						}
					}
					if (!found)
					{
						m_NominalMapping[i] = - 1;
					}
				}
			}
			setOutputFormat(instanceInfo);
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
		/// <exception cref="IllegalStateException">if no input format has been set.
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
			if (instance.isMissing(m_AttIndex.Index))
			{
				if (!get_MatchMissingValues())
				{
					push((Instance) instance.copy());
					return true;
				}
				else
				{
					return false;
				}
			}
			if (Numeric)
			{
				if (!m_Values.Invert)
				{
					if (instance.value_Renamed(m_AttIndex.Index) < m_Value)
					{
						push((Instance) instance.copy());
						return true;
					}
				}
				else
				{
					if (instance.value_Renamed(m_AttIndex.Index) >= m_Value)
					{
						push((Instance) instance.copy());
						return true;
					}
				}
			}
			if (Nominal)
			{
				if (m_Values.isInRange((int) instance.value_Renamed(m_AttIndex.Index)))
				{
					Instance temp = (Instance) instance.copy();
					if (get_ModifyHeader())
					{
						temp.setValue(m_AttIndex.Index, m_NominalMapping[(int) instance.value_Renamed(m_AttIndex.Index)]);
					}
					push(temp);
					return true;
				}
			}
			return false;
		}
		
		
		/// <summary> Gets whether the header will be modified when selecting on nominal
		/// attributes.
		/// 
		/// </summary>
		/// <returns> true if so.
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("When selecting on nominal attributes, removes header references to excluded values.")  </attribute>
		/// <property>   </property>
		public virtual bool get_ModifyHeader()
		{
			
			return m_ModifyHeader;
		}
		
		/// <summary> Sets whether the header will be modified when selecting on nominal
		/// attributes.
		/// 
		/// </summary>
		/// <param name="newModifyHeader">true if so.
		/// </param>
		/// <property>   </property>
		public virtual void  set_ModifyHeader(bool newModifyHeader)
		{
			
			m_ModifyHeader = newModifyHeader;
		}
		
		
		/// <summary> Get the index of the attribute used.
		/// 
		/// </summary>
		/// <returns> the index of the attribute
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Choose attribute to be used for selection (default last).")  </attribute>
		/// <property>   </property>
		public virtual System.String get_AttributeIndex()
		{
			
			return m_AttIndex.getSingleIndex();
		}
		
		/// <summary> Sets index of the attribute used.
		/// 
		/// </summary>
		/// <param name="index">the index of the attribute
		/// </param>
		/// <property>   </property>
		public virtual void  set_AttributeIndex(System.String attIndex)
		{
			
			m_AttIndex.setSingleIndex(attIndex);
		}
		
		/// <summary> Get the split point used for numeric selection
		/// 
		/// </summary>
		/// <returns> the numeric split point
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Numeric value to be used for selection on numeric attribute. Instances with values smaller than given value will be selected.")  </attribute>
		/// <property>   </property>
		public virtual double get_SplitPoint()
		{
			
			return m_Value;
		}
		
		/// <summary> Split point to be used for selection on numeric attribute.
		/// 
		/// </summary>
		/// <param name="value">the split point
		/// </param>
		/// <property>   </property>
		public virtual void  set_SplitPoint(double value_Renamed)
		{
			
			m_Value = value_Renamed;
		}
		
		
		/// <summary> Gets whether missing values are counted as a match.
		/// 
		/// </summary>
		/// <returns> true if missing values are counted as a match.
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Missing values count as a match. This setting is independent of the invertSelection option.")  </attribute>
		/// <property>   </property>
		public virtual bool get_MatchMissingValues()
		{
			
			return m_MatchMissingValues;
		}
		
		/// <summary> Sets whether missing values are counted as a match.
		/// 
		/// </summary>
		/// <param name="newMatchMissingValues">true if missing values are counted as a match.
		/// </param>
		/// <property>   </property>
		public virtual void  set_MatchMissingValues(bool newMatchMissingValues)
		{
			
			m_MatchMissingValues = newMatchMissingValues;
		}
		
		
		/// <summary> Get whether the supplied columns are to be removed or kept
		/// 
		/// </summary>
		/// <returns> true if the supplied columns will be kept
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Invert matching sense.")  </attribute>
		/// <property>   </property>
		public virtual bool get_InvertSelection()
		{
			
			return !m_Values.Invert;
		}
		
		/// <summary> Set whether selected values should be removed or kept. If true the 
		/// selected values are kept and unselected values are deleted. 
		/// 
		/// </summary>
		/// <param name="invert">the new invert setting
		/// </param>
		/// <property>   </property>
		public virtual void  set_InvertSelection(bool invert)
		{
			
			m_Values.Invert=!invert;
		}
		
		
		
		/// <summary> Get the set of nominal value indices that will be used for selection
		/// 
		/// </summary>
		/// <returns> rangeList a string representing the list of nominal indices.
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Range of label indices to be used for selection on nominal attribute. First and last are valid indexes.")  </attribute>
		/// <property>   </property>
		public virtual System.String get_NominalIndices()
		{
			
			return m_Values.Ranges;
		}
		
		/// <summary> Set which nominal labels are to be included in the selection.
		/// 
		/// </summary>
		/// <param name="rangeList">a string representing the list of nominal indices.
		/// eg: first-3,5,6-last
		/// </param>
		/// <exception cref="InvalidArgumentException">if an invalid range list is supplied
		/// </exception>
		/// <property>   </property>
		public virtual void  set_NominalIndices(System.String rangeList)
		{
			
			m_Values.Ranges=rangeList;
		}
	}
}