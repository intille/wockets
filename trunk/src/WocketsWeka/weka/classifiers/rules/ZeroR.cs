/*    ZeroR.java
*    Copyright (C) 1999 Eibe Frank
*/
using System;
using Classifier = weka.classifiers.Classifier;
using Evaluation = weka.classifiers.Evaluation;
using weka.core;
using System.IO;
namespace weka.classifiers.rules
{
	
	/// <summary> Class for building and using a 0-R classifier. Predicts the mean
	/// (for a numeric class) or the mode (for a nominal class).
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.11 $
	/// </version>
	/// <attribute>  System.ComponentModel.DescriptionAttribute("Class for building and using a 0-R classifier. Predicts the mean (for a numeric class) or the mode (for a nominal class).")  </attribute>
#if !PocketPC	
    [Serializable]
#endif
	public class ZeroR:Classifier, WeightedInstancesHandler
	{
		/// <summary>The class value 0R predicts. </summary>
		private double m_ClassValue;
		/// <summary>The number of instances in each class (null if class numeric). </summary>
		private double[] m_Counts;
		/// <summary>The class attribute. </summary>
		private weka.core.Attribute m_Class;
        
        public override void toXML(TextWriter tw)
        {
 
        }


        public override void buildClassifier(string fileName, Instances instances)
        {
        }
		/// <summary> Generates the classifier.
		/// 
		/// </summary>
		/// <param name="instances">set of instances serving as training data 
		/// </param>
		/// <exception cref="Exception">if the classifier has not been generated successfully
		/// </exception>
		public override void  buildClassifier(Instances instances)
		{
			
			double sumOfWeights = 0;
			
			m_Class = instances.classAttribute();
			m_ClassValue = 0;
			switch (instances.classAttribute().type())
			{
				
				case weka.core.Attribute.NUMERIC: 
					m_Counts = null;
					break;

                case weka.core.Attribute.NOMINAL: 
					m_Counts = new double[instances.numClasses()];
					for (int i = 0; i < m_Counts.Length; i++)
					{
						m_Counts[i] = 1;
					}
					sumOfWeights = instances.numClasses();
					break;
				
				default: 
					throw new System.Exception("ZeroR can only handle nominal and numeric class" + " attributes.");
				
			}
			System.Collections.IEnumerator enu = instances.enumerateInstances();
			//UPGRADE_TODO: Method 'java.util.Enumeration.hasMoreElements' was converted to 'System.Collections.IEnumerator.MoveNext' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationhasMoreElements'"
			while (enu.MoveNext())
			{
				//UPGRADE_TODO: Method 'java.util.Enumeration.nextElement' was converted to 'System.Collections.IEnumerator.Current' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationnextElement'"
				Instance instance = (Instance) enu.Current;
				if (!instance.classIsMissing())
				{
					if (instances.classAttribute().Nominal)
					{
						//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
						m_Counts[(int) instance.classValue()] += instance.weight();
					}
					else
					{
						m_ClassValue += instance.weight() * instance.classValue();
					}
					sumOfWeights += instance.weight();
				}
			}
			if (instances.classAttribute().Numeric)
			{
				if (Utils.gr(sumOfWeights, 0))
				{
					m_ClassValue /= sumOfWeights;
				}
			}
			else
			{
				m_ClassValue = Utils.maxIndex(m_Counts);
				Utils.normalize(m_Counts, sumOfWeights);
			}
		}
		
		/// <summary> Classifies a given instance.
		/// 
		/// </summary>
		/// <param name="instance">the instance to be classified
		/// </param>
		/// <returns> index of the predicted class
		/// </returns>
		public override double classifyInstance(Instance instance)
		{
			
			return m_ClassValue;
		}
		
		/// <summary> Calculates the class membership probabilities for the given test instance.
		/// 
		/// </summary>
		/// <param name="instance">the instance to be classified
		/// </param>
		/// <returns> predicted class probability distribution
		/// </returns>
		/// <exception cref="Exception">if class is numeric
		/// </exception>
		public override double[] distributionForInstance(Instance instance)
		{
			
			if (m_Counts == null)
			{
				double[] result = new double[1];
				result[0] = m_ClassValue;
				return result;
			}
			else
			{
				return (double[]) m_Counts.Clone();
			}
		}
		
		/// <summary> Returns a description of the classifier.
		/// 
		/// </summary>
		/// <returns> a description of the classifier as a string.
		/// </returns>
		public override System.String ToString()
		{
			
			if (m_Class == null)
			{
				return "ZeroR: No model built yet.";
			}
			if (m_Counts == null)
			{
				return "ZeroR predicts class value: " + m_ClassValue;
			}
			else
			{
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				return "ZeroR predicts class value: " + m_Class.value_Renamed((int) m_ClassValue);
			}
		}
		//UPGRADE_TODO: The following method was automatically generated and it must be implemented in order to preserve the class logic. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1232'"
		override public System.Object Clone()
		{
			return null;
		}
	}
}