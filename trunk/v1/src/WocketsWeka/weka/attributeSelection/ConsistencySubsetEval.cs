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
*    ConsistencySubsetEval.java
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
	
	/// <summary> Consistency attribute subset evaluator. <p>
	/// 
	/// For more information see: <br>
	/// Liu, H., and Setiono, R., (1996). A probabilistic approach to feature 
	/// selection - A filter solution. In 13th International Conference on 
	/// Machine Learning (ICML'96), July 1996, pp. 319-327. Bari, Italy. 
	/// 
	/// </summary>
	/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.10 $
	/// </version>
	[Serializable]
	public class ConsistencySubsetEval:SubsetEvaluator
	{
		
		/// <summary>training instances </summary>
		private Instances m_trainInstances;
		
		/// <summary>class index </summary>
		private int m_classIndex;
		
		/// <summary>number of attributes in the training data </summary>
		private int m_numAttribs;
		
		/// <summary>number of instances in the training data </summary>
		private int m_numInstances;
		
		/// <summary>Discretise numeric attributes </summary>
		private Discretize m_disTransform;
		
		/// <summary>Hash table for evaluating feature subsets </summary>
		private System.Collections.Hashtable m_table;
		
		//UPGRADE_NOTE: Field 'EnclosingInstance' was added to class 'hashKey' to access its enclosing instance. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1019'"
		/// <summary> Class providing keys to the hash table.</summary>
		[Serializable]
		public class hashKey
		{
			private void  InitBlock(ConsistencySubsetEval enclosingInstance)
			{
				this.enclosingInstance = enclosingInstance;
			}
			private ConsistencySubsetEval enclosingInstance;
			public ConsistencySubsetEval Enclosing_Instance
			{
				get
				{
					return enclosingInstance;
				}
				
			}
			
			/// <summary>Array of attribute values for an instance </summary>
			private double[] attributes;
			
			/// <summary>True for an index if the corresponding attribute value is missing. </summary>
			private bool[] missing;
			
			/// <summary>The values </summary>
			private System.String[] values;
			
			/// <summary>The key </summary>
			private int key;
			
			/// <summary> Constructor for a hashKey
			/// 
			/// </summary>
			/// <param name="t">an instance from which to generate a key
			/// </param>
			/// <param name="numAtts">the number of attributes
			/// </param>
			public hashKey(ConsistencySubsetEval enclosingInstance, Instance t, int numAtts)
			{
				InitBlock(enclosingInstance);
				
				int i;
				int cindex = t.classIndex();
				
				key = - 999;
				attributes = new double[numAtts];
				missing = new bool[numAtts];
				for (i = 0; i < numAtts; i++)
				{
					if (i == cindex)
					{
						missing[i] = true;
					}
					else
					{
						if ((missing[i] = t.isMissing(i)) == false)
						{
							attributes[i] = t.value_Renamed(i);
						}
					}
				}
			}
			
			/// <summary> Convert a hash entry to a string
			/// 
			/// </summary>
			/// <param name="t">the set of instances
			/// </param>
			/// <param name="maxColWidth">width to make the fields
			/// </param>
			public virtual System.String toString(Instances t, int maxColWidth)
			{
				
				int i;
				int cindex = t.classIndex();
				System.Text.StringBuilder text = new System.Text.StringBuilder();
				
				for (i = 0; i < attributes.Length; i++)
				{
					if (i != cindex)
					{
						if (missing[i])
						{
							text.Append("?");
							for (int j = 0; j < maxColWidth; j++)
							{
								text.Append(" ");
							}
						}
						else
						{
							//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
							System.String ss = t.attribute(i).value_Renamed((int) attributes[i]);
							System.Text.StringBuilder sb = new System.Text.StringBuilder(ss);
							
							for (int j = 0; j < (maxColWidth - ss.Length + 1); j++)
							{
								sb.Append(" ");
							}
							text.Append(sb);
						}
					}
				}
				return text.ToString();
			}
			
			/// <summary> Constructor for a hashKey
			/// 
			/// </summary>
			/// <param name="t">an array of feature values
			/// </param>
			public hashKey(ConsistencySubsetEval enclosingInstance, double[] t)
			{
				InitBlock(enclosingInstance);
				
				int i;
				int l = t.Length;
				
				key = - 999;
				attributes = new double[l];
				missing = new bool[l];
				for (i = 0; i < l; i++)
				{
					//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
					if (t[i] == System.Double.MaxValue)
					{
						missing[i] = true;
					}
					else
					{
						missing[i] = false;
						attributes[i] = t[i];
					}
				}
			}
			
			/// <summary> Calculates a hash code
			/// 
			/// </summary>
			/// <returns> the hash code as an integer
			/// </returns>
			public override int GetHashCode()
			{
				
				int hv = 0;
				
				if (key != - 999)
					return key;
				for (int i = 0; i < attributes.Length; i++)
				{
					if (missing[i])
					{
						hv += (i * 13);
					}
					else
					{
						hv = (int) (hv + (i * 5 * (attributes[i] + 1)));
					}
				}
				if (key == - 999)
				{
					key = hv;
				}
				return hv;
			}
			
			/// <summary> Tests if two instances are equal
			/// 
			/// </summary>
			/// <param name="b">a key to compare with
			/// </param>
			public  override bool Equals(System.Object b)
			{
				
				if ((b == null) || !(b.GetType().Equals(this.GetType())))
				{
					return false;
				}
				bool ok = true;
				bool l;
				if (b is hashKey)
				{
					hashKey n = (hashKey) b;
					for (int i = 0; i < attributes.Length; i++)
					{
						l = n.missing[i];
						if (missing[i] || l)
						{
							if ((missing[i] && !l) || (!missing[i] && l))
							{
								ok = false;
								break;
							}
						}
						else
						{
							if (attributes[i] != n.attributes[i])
							{
								ok = false;
								break;
							}
						}
					}
				}
				else
				{
					return false;
				}
				return ok;
			}
			
			/// <summary> Prints the hash code</summary>
			public virtual void  print_hash_code()
			{
				
				System.Console.Out.WriteLine("Hash val: " + GetHashCode());
			}
		}
		
		/// <summary> Returns a string describing this search method</summary>
		/// <returns> a description of the search suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String globalInfo()
		{
			return "ConsistencySubsetEval :\n\nEvaluates the worth of a subset of " + "attributes by the level of consistency in the class values when the " + "training instances are projected onto the subset of attributes. " + "\n\nConsistency of any subset can never be lower than that of the " + "full set of attributes, hence the usual practice is to use this " + "subset evaluator in conjunction with a Random or Exhaustive search " + "which looks for the smallest subset with consistency equal to that " + "of the full set of attributes.\n";
		}
		
		/// <summary> Constructor. Calls restOptions to set default options
		/// 
		/// </summary>
		public ConsistencySubsetEval()
		{
			resetOptions();
		}
		
		/// <summary> reset to defaults</summary>
		private void  resetOptions()
		{
			m_trainInstances = null;
		}
		
		/// <summary> Generates a attribute evaluator. Has to initialize all fields of the 
		/// evaluator that are not being set via options.
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
			if (m_classIndex < 0)
			{
				throw new System.Exception("Consistency subset evaluator requires a class " + "attribute!");
			}
			
			if (m_trainInstances.classAttribute().Numeric)
			{
				throw new System.Exception("Consistency subset evaluator can't handle a " + "numeric class attribute!");
			}
			
			m_numAttribs = m_trainInstances.numAttributes();
			m_numInstances = m_trainInstances.numInstances();
			
			m_disTransform = new Discretize();
            m_disTransform.UseBetterEncoding = true; //.setUseBetterEncoding(true);
			m_disTransform.setInputFormat(m_trainInstances);
			m_trainInstances = Filter.useFilter(m_trainInstances, m_disTransform);
		}
		
		/// <summary> Evaluates a subset of attributes
		/// 
		/// </summary>
		/// <param name="subset">a bitset representing the attribute subset to be 
		/// evaluated 
		/// </param>
		/// <exception cref="Exception">if the subset could not be evaluated
		/// </exception>
		public override double evaluateSubset(System.Collections.BitArray subset)
		{
			int[] fs;
			int i;
			int count = 0;
			
			for (i = 0; i < m_numAttribs; i++)
			{
				if (subset.Get(i))
				{
					count++;
				}
			}
			
			double[] instArray = new double[count];
			int index = 0;
			fs = new int[count];
			for (i = 0; i < m_numAttribs; i++)
			{
				if (subset.Get(i))
				{
					fs[index++] = i;
				}
			}
			
			// create new hash table
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			m_table = System.Collections.Hashtable.Synchronized(new System.Collections.Hashtable((int) (m_numInstances * 1.5)));
			
			for (i = 0; i < m_numInstances; i++)
			{
				Instance inst = m_trainInstances.instance(i);
				for (int j = 0; j < fs.Length; j++)
				{
					if (fs[j] == m_classIndex)
					{
						throw new System.Exception("A subset should not contain the class!");
					}
					if (inst.isMissing(fs[j]))
					{
						//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
						instArray[j] = System.Double.MaxValue;
					}
					else
					{
						instArray[j] = inst.value_Renamed(fs[j]);
					}
				}
				insertIntoTable(inst, instArray);
			}
			
			return consistencyCount();
		}
		
		/// <summary> calculates the level of consistency in a dataset using a subset of
		/// features. The consistency of a hash table entry is the total number
		/// of instances hashed to that location minus the number of instances in
		/// the largest class hashed to that location. The total consistency is
		/// 1.0 minus the sum of the individual consistencies divided by the
		/// total number of instances.
		/// </summary>
		/// <returns> the consistency of the hash table as a value between 0 and 1.
		/// </returns>
		private double consistencyCount()
		{
			System.Collections.IEnumerator e = m_table.Keys.GetEnumerator();
			double[] classDist;
			double count = 0.0;
			
			//UPGRADE_TODO: Method 'java.util.Enumeration.hasMoreElements' was converted to 'System.Collections.IEnumerator.MoveNext' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationhasMoreElements'"
			while (e.MoveNext())
			{
				//UPGRADE_TODO: Method 'java.util.Enumeration.nextElement' was converted to 'System.Collections.IEnumerator.Current' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationnextElement'"
				hashKey tt = (hashKey) e.Current;
				classDist = (double[]) m_table[tt];
				count += Utils.sum(classDist);
				int max = Utils.maxIndex(classDist);
				count -= classDist[max];
			}
			
			count /= (double) m_numInstances;
			return (1.0 - count);
		}
		
		/// <summary> Inserts an instance into the hash table
		/// 
		/// </summary>
		/// <param name="inst">instance to be inserted
		/// </param>
		/// <param name="instA">the instance to be inserted as an array of attribute
		/// values.
		/// </param>
		/// <exception cref="Exception">if the instance can't be inserted
		/// </exception>
		private void  insertIntoTable(Instance inst, double[] instA)
		{
			
			double[] tempClassDist2;
			double[] newDist;
			hashKey thekey;
			
			thekey = new hashKey(this, instA);
			
			// see if this one is already in the table
			tempClassDist2 = (double[]) m_table[thekey];
			if (tempClassDist2 == null)
			{
				newDist = new double[m_trainInstances.classAttribute().numValues()];
				newDist[(int) inst.classValue()] = inst.weight();
				
				// add to the table
				m_table[thekey] = newDist;
			}
			else
			{
				// update the distribution for this instance
				tempClassDist2[(int) inst.classValue()] += inst.weight();
				
				// update the table
				m_table[thekey] = tempClassDist2;
			}
		}
		
		/// <summary> returns a description of the evaluator</summary>
		/// <returns> a description of the evaluator as a String.
		/// </returns>
		public override System.String ToString()
		{
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			
			if (m_trainInstances == null)
			{
				text.Append("\tConsistency subset evaluator has not been built yet\n");
			}
			else
			{
				text.Append("\tConsistency Subset Evaluator\n");
			}
			
			return text.ToString();
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
				System.Console.Out.WriteLine(AttributeSelection.SelectAttributes(new ConsistencySubsetEval(), args));
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