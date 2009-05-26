/*
*    ClassifierSplitModel.java
*    Copyright (C) 1999 Eibe Frank
*
*/
using System;
using weka.core;
using System.IO;
namespace weka.classifiers.trees.j48
{
	
	/// <summary> Abstract class for classification models that can be used 
	/// recursively to split the data.
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.8 $
	/// </version>
#if !PocketPC
    [Serializable()]  
#endif
	public abstract class ClassifierSplitModel : System.ICloneable
	{
		
		/// <summary>Distribution of class values. </summary>
		protected internal Distribution m_distribution;
		
		/// <summary>Number of created subsets. </summary>
		protected internal int m_numSubsets;
		
		/// <summary> Allows to clone a model (shallow copy).</summary>
		public virtual System.Object Clone()
		{
			
			System.Object clone = null;
			
			try
			{
				clone = base.MemberwiseClone();
			}
			//UPGRADE_NOTE: Exception 'java.lang.CloneNotSupportedException' was converted to 'System.Exception' which has different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1100'"
			catch (System.Exception e)
			{
                System.Console.WriteLine(e.StackTrace+" "+e.Message);
			}
			return clone;
		}


        public abstract void toXML(TextWriter tw);
		/// <summary> Builds the classifier split model for the given set of instances.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public abstract void  buildClassifier(Instances instances);
		
		/// <summary> Checks if generated model is valid.</summary>
		public bool checkModel()
		{
			
			if (m_numSubsets > 0)
				return true;
			else
				return false;
		}
		
		/// <summary> Classifies a given instance.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public double classifyInstance(Instance instance)
		{
			
			int theSubset;
			
			theSubset = whichSubset(instance);
			if (theSubset > - 1)
				return (double) m_distribution.maxClass(theSubset);
			else
				return (double) m_distribution.maxClass();
		}
		
		/// <summary> Gets class probability for instance.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public virtual double classProb(int classIndex, Instance instance, int theSubset)
		{
			
			if (theSubset > - 1)
			{
				return m_distribution.prob(classIndex, theSubset);
			}
			else
			{
				double[] weights = GetWeights(instance);
				if (weights == null)
				{
					return m_distribution.prob(classIndex);
				}
				else
				{
					double prob = 0;
					for (int i = 0; i < weights.Length; i++)
					{
						prob += weights[i] * m_distribution.prob(classIndex, i);
					}
					return prob;
				}
			}
		}
		
		/// <summary> Gets class probability for instance.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public virtual double classProbLaplace(int classIndex, Instance instance, int theSubset)
		{
			
			if (theSubset > - 1)
			{
				return m_distribution.laplaceProb(classIndex, theSubset);
			}
			else
			{
				double[] weights = GetWeights(instance);
				if (weights == null)
				{
					return m_distribution.laplaceProb(classIndex);
				}
				else
				{
					double prob = 0;
					for (int i = 0; i < weights.Length; i++)
					{
						prob += weights[i] * m_distribution.laplaceProb(classIndex, i);
					}
					return prob;
				}
			}
		}
		
		/// <summary> Returns coding costs of model. Returns 0 if not overwritten.</summary>
		public virtual double codingCost()
		{
			
			return 0;
		}
		
		/// <summary> Returns the distribution of class values induced by the model.</summary>
		public Distribution distribution()
		{
			
			return m_distribution;
		}
		
		/// <summary> Prints left side of condition satisfied by instances.
		/// 
		/// </summary>
		/// <param name="data">the data.
		/// </param>
		public abstract System.String leftSide(Instances data);
		
		/// <summary> Prints left side of condition satisfied by instances in subset index.</summary>
		public abstract System.String rightSide(int index, Instances data);
		
		/// <summary> Prints label for subset index of instances (eg class).
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public System.String dumpLabel(int index, Instances data)
		{
			
			System.Text.StringBuilder text;
			
			text = new System.Text.StringBuilder();
			text.Append(((Instances) data).classAttribute().value_Renamed(m_distribution.maxClass(index)));
			text.Append(" (" + Utils.roundDouble(m_distribution.perBag(index), 2));
			if (Utils.gr(m_distribution.numIncorrect(index), 0))
				text.Append("/" + Utils.roundDouble(m_distribution.numIncorrect(index), 2));
			text.Append(")");
			
			return text.ToString();
		}
		
		public System.String sourceClass(int index, Instances data)
		{
			
			System.Console.Error.WriteLine("sourceClass");
			return (new System.Text.StringBuilder(m_distribution.maxClass(index))).ToString();
		}
		
		public abstract System.String sourceExpression(int index, Instances data);
		
		/// <summary> Prints the split model.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public System.String dumpModel(Instances data)
		{
			
			System.Text.StringBuilder text;
			int i;
			
			text = new System.Text.StringBuilder();
			for (i = 0; i < m_numSubsets; i++)
			{
				text.Append(leftSide(data) + rightSide(i, data) + ": ");
				text.Append(dumpLabel(i, data) + "\n");
			}
			return text.ToString();
		}
		
		/// <summary> Returns the number of created subsets for the split.</summary>
		public int numSubsets()
		{
			
			return m_numSubsets;
		}
		
		/// <summary> Sets distribution associated with model.</summary>
		public virtual void  resetDistribution(Instances data)
		{
			
			m_distribution = new Distribution(data, this);
		}
		
		/// <summary> Splits the given set of instances into subsets.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public Instances[] split(Instances data)
		{
			
			Instances[] instances = new Instances[m_numSubsets];
			double[] weights;
			double newWeight;
			Instance instance;
			int subset, i, j;
			
			for (j = 0; j < m_numSubsets; j++)
				instances[j] = new Instances((Instances) data, data.numInstances());
			for (i = 0; i < data.numInstances(); i++)
			{
				instance = ((Instances) data).instance(i);
				weights = GetWeights(instance);
				subset = whichSubset(instance);
				if (subset > - 1)
					instances[subset].add(instance);
				else
					for (j = 0; j < m_numSubsets; j++)
						if (Utils.gr(weights[j], 0))
						{
							newWeight = weights[j] * instance.weight();
							instances[j].add(instance);
							instances[j].lastInstance().Weight = newWeight;
						}
			}
			for (j = 0; j < m_numSubsets; j++)
				instances[j].compactify();
			
			return instances;
		}
		
		/// <summary> Returns weights if instance is assigned to more than one subset.
		/// Returns null if instance is only assigned to one subset.
		/// </summary>
		public abstract double[] GetWeights(Instance instance);
		
		/// <summary> Returns index of subset instance is assigned to.
		/// Returns -1 if instance is assigned to more than one subset.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public abstract int whichSubset(Instance instance);
	}
}