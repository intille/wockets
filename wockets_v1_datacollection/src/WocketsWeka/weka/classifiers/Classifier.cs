/*
*    Classifier.java
*    Copyright (C) 1999 Eibe Frank, Len Trigg
*
*/
using System;
using weka.core;
using System.IO;

namespace weka.classifiers
{
	
	/// <summary> Abstract classifier. All schemes for numeric or nominal prediction in
	/// Weka extend this class. Note that a classifier MUST either implement
	/// distributionForInstance() or classifyInstance().
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <author>  Len Trigg (trigg@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.11.2.1 $
	/// </version>
	/// <attribute>  System.ComponentModel.CategoryAttribute("Classifiers")  </attribute>
#if !PocketPC
    [Serializable()]  
#endif
	public abstract class Classifier : System.ICloneable
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Get whether debugging is turned on.
		/// 
		/// </summary>
		/// <returns> true if debugging output is on
		/// </returns>
		/// <summary> Set debugging mode.
		/// 
		/// </summary>
		/// <param name="debug">true if debug output should be printed
		/// </param>
		virtual public bool Debug
		{
			get
			{
				
				return m_Debug;
			}
			
			set
			{
				
				m_Debug = value;
			}
			
		}
		//code added by Alain Espinosa
		public virtual Classifier GetThis()
		{
			return this;
		}
		//end of code
		/// <summary>Whether the classifier is run in debug mode. </summary>
		protected internal bool m_Debug = false;
		
		/// <summary> Generates a classifier. Must initialize all fields of the classifier
		/// that are not being set via options (ie. multiple calls of buildClassifier
		/// must always lead to the same result). Must not change the dataset
		/// in any way.
		/// 
		/// </summary>
		/// <param name="data">set of instances serving as training data 
		/// </param>
		/// <exception cref="Exception">if the classifier has not been 
		/// generated successfully
		/// </exception>
		public abstract void  buildClassifier(Instances data);


        public abstract void buildClassifier(string fileName, Instances instances);

        public abstract void toXML(TextWriter tw);
		
		/// <summary> Classifies the given test instance. The instance has to belong to a
		/// dataset when it's being classified. Note that a classifier MUST
		/// implement either this or distributionForInstance().
		/// 
		/// </summary>
		/// <param name="instance">the instance to be classified
		/// </param>
		/// <returns> the predicted most likely class for the instance or 
		/// Instance.missingValue() if no prediction is made
		/// </returns>
		/// <exception cref="Exception">if an error occurred during the prediction
		/// </exception>
		public virtual double classifyInstance(Instance instance)
		{
			double[] dist = distributionForInstance(instance);
			if (dist == null)
			{
				throw new System.Exception("Null distribution predicted");
			}
			switch (instance.classAttribute().type())
			{
				
				case weka.core.Attribute.NOMINAL: 
					double max = 0;
					int maxIndex = 0;
					
					for (int i = 0; i < dist.Length; i++)
					{
						if (dist[i] > max)
						{
							maxIndex = i;
							max = dist[i];
						}
					}
					if (max > 0)
					{
						return maxIndex;
					}
					else
					{
						return Instance.missingValue();
					}				

                case weka.core.Attribute.NUMERIC: 
					return dist[0];
				
				default: 
					return Instance.missingValue();
				
			}
		}
		
		/// <summary> Predicts the class memberships for a given instance. If
		/// an instance is unclassified, the returned array elements
		/// must be all zero. If the class is numeric, the array
		/// must consist of only one element, which contains the
		/// predicted value. Note that a classifier MUST implement
		/// either this or classifyInstance().
		/// 
		/// </summary>
		/// <param name="instance">the instance to be classified
		/// </param>
		/// <returns> an array containing the estimated membership 
		/// probabilities of the test instance in each class 
		/// or the numeric prediction
		/// </returns>
		/// <exception cref="Exception">if distribution could not be 
		/// computed successfully
		/// </exception>
		public virtual double[] distributionForInstance(Instance instance)
		{
			double[] dist = new double[instance.numClasses()];
			switch (instance.classAttribute().type())
			{
				
				case weka.core.Attribute.NOMINAL: 
					double classification = classifyInstance(instance);
					if (Instance.isMissingValue(classification))
					{
						return dist;
					}
					else
					{
						//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
						dist[(int) classification] = 1.0;
					}
					return dist;

                case weka.core.Attribute.NUMERIC: 
					dist[0] = classifyInstance(instance);
					return dist;
				
				default: 
					return dist;
				
			}
		}
		
		/// <summary> Creates a new instance of a classifier given it's class name and
		/// (optional) arguments to pass to it's setOptions method. If the
		/// classifier implements OptionHandler and the options parameter is
		/// non-null, the classifier will have it's options set.
		/// 
		/// </summary>
		/// <param name="classifierName">the fully qualified class name of the classifier
		/// </param>
		/// <param name="options">an array of options suitable for passing to setOptions. May
		/// be null.
		/// </param>
		/// <returns> the newly created classifier, ready for use.
		/// </returns>
		/// <exception cref="Exception">if the classifier name is invalid, or the options
		/// supplied are not acceptable to the classifier
		/// </exception>
		public static Classifier forName(System.String classifierName, System.String[] options)
		{
			return (Classifier) Utils.forName(typeof(Classifier), classifierName, options);
		}
		
		/// <summary> Creates a deep copy of the given classifier using serialization.
		/// 
		/// </summary>
		/// <param name="model">the classifier to copy
		/// </param>
		/// <returns> a deep copy of the classifier
		/// </returns>
		/// <exception cref="Exception">if an error occurs
		/// </exception>
		public static Classifier makeCopy(Classifier model)
		{
			
			return (Classifier) model.Clone();
		}
		
		/// <summary> Creates a given number of deep copies of the given classifier using serialization.
		/// 
		/// </summary>
		/// <param name="model">the classifier to copy
		/// </param>
		/// <param name="num">the number of classifier copies to create.
		/// </param>
		/// <returns> an array of classifiers.
		/// </returns>
		/// <exception cref="Exception">if an error occurs
		/// </exception>
		public static Classifier[] makeCopies(Classifier model, int num)
		{
			
			if (model == null)
			{
				throw new System.Exception("No model classifier set");
			}
			Classifier[] classifiers = new Classifier[num];
			
			for (int i = 0; i < classifiers.Length; i++)
			{
                classifiers[i] = (Classifier)makeCopy(model);
			}
			return classifiers;
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String debugTipText()
		{
			return "If set to true, classifier may output additional info to " + "the console.";
		}
		//UPGRADE_TODO: The following method was automatically generated and it must be implemented in order to preserve the class logic. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1232'"
		abstract public System.Object Clone();
	}
}