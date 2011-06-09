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
*    NumericToBinary.java
*    Copyright (C) 1999 Eibe Frank
*
*/
using System;
using weka.filters;
using weka.core;
namespace weka.filters.unsupervised.attribute
{
	
	/// <summary> Converts all numeric attributes into binary attributes (apart from
	/// the class attribute): if the value of the numeric attribute is
	/// exactly zero, the value of the new attribute will be zero. If the
	/// value of the numeric attribute is missing, the value of the new
	/// attribute will be missing. Otherwise, the value of the new
	/// attribute will be one. The new attributes will nominal.<p>
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz) 
	/// </author>
	/// <version>  $Revision: 1.3 $ 
	/// </version>
	[Serializable]
	public class NumericToBinary:PotentialClassIgnorer, UnsupervisedFilter, StreamableFilter
	{
		
		/// <summary> Returns a string describing this filter
		/// 
		/// </summary>
		/// <returns> a description of the filter suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String globalInfo()
		{
			
			return "Converts all numeric attributes into binary attributes (apart from " + "the class attribute, if set): if the value of the numeric attribute is " + "exactly zero, the value of the new attribute will be zero. If the " + "value of the numeric attribute is missing, the value of the new " + "attribute will be missing. Otherwise, the value of the new " + "attribute will be one. The new attributes will nominal.";
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
			setOutputFormat();
			return true;
		}
		
		/// <summary> Input an instance for filtering.
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
			convertInstance(instance);
			return true;
		}
		
		/// <summary> Set the output format. </summary>
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
				if ((j == newClassIndex) || (!att.Numeric))
				{
					newAtts.addElement(att.copy());
				}
				else
				{
					attributeName = new System.Text.StringBuilder(att.name() + "_binarized");
					vals = new FastVector(2);
					vals.addElement("0"); vals.addElement("1");
                    newAtts.addElement(new weka.core.Attribute(attributeName.ToString(), vals));
				}
			}
			outputFormat = new Instances(getInputFormat().relationName(), newAtts, 0);
			outputFormat.ClassIndex = newClassIndex;
			setOutputFormat(outputFormat);
		}
		
		/// <summary> Convert a single instance over. The converted instance is 
		/// added to the end of the output queue.
		/// 
		/// </summary>
		/// <param name="instance">the instance to convert
		/// </param>
		private void  convertInstance(Instance instance)
		{
			
			Instance inst = null;
			if (instance is SparseInstance)
			{
				double[] vals = new double[instance.numValues()];
				int[] newIndices = new int[instance.numValues()];
				for (int j = 0; j < instance.numValues(); j++)
				{
                    weka.core.Attribute att = getInputFormat().attribute(instance.index(j));
					if ((!att.Numeric) || (instance.index(j) == getInputFormat().classIndex()))
					{
						vals[j] = instance.valueSparse(j);
					}
					else
					{
						if (instance.isMissingSparse(j))
						{
							vals[j] = instance.valueSparse(j);
						}
						else
						{
							vals[j] = 1;
						}
					}
					newIndices[j] = instance.index(j);
				}
				inst = new SparseInstance(instance.weight(), vals, newIndices, outputFormatPeek().numAttributes());
			}
			else
			{
				double[] vals = new double[outputFormatPeek().numAttributes()];
				for (int j = 0; j < getInputFormat().numAttributes(); j++)
				{
                    weka.core.Attribute att = getInputFormat().attribute(j);
					if ((!att.Numeric) || (j == getInputFormat().classIndex()))
					{
						vals[j] = instance.value_Renamed(j);
					}
					else
					{
						if (instance.isMissing(j) || (instance.value_Renamed(j) == 0))
						{
							vals[j] = instance.value_Renamed(j);
						}
						else
						{
							vals[j] = 1;
						}
					}
				}
				inst = new Instance(instance.weight(), vals);
			}
			inst.Dataset = instance.dataset();
			push(inst);
		}
		

	}
}