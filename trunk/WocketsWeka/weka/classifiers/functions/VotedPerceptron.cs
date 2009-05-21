/*    VotedPerceptron.java
*    Copyright (C) 1999 Eibe Frank
*/
using System;
using Classifier = weka.classifiers.Classifier;
using Evaluation = weka.classifiers.Evaluation;
//UPGRADE_TODO: The type 'weka.filters.unsupervised.attribute.NominalToBinary' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using NominalToBinary = weka.filters.unsupervised.attribute.NominalToBinary;
//UPGRADE_TODO: The type 'weka.filters.unsupervised.attribute.ReplaceMissingValues' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using ReplaceMissingValues = weka.filters.unsupervised.attribute.ReplaceMissingValues;
using Filter = weka.filters.Filter;
using weka.core;
using System.IO;
namespace weka.classifiers.functions
{
	
	/// <summary> Implements the voted perceptron algorithm by Freund and
	/// Schapire. Globally replaces all missing values, and transforms
	/// nominal attributes into binary ones. For more information, see<p>
	/// 
	/// Y. Freund and R. E. Schapire (1998). <i> Large margin
	/// classification using the perceptron algorithm</i>.  Proc. 11th
	/// Annu. Conf. on Comput. Learning Theory, pp. 209-217, ACM Press, New
	/// York, NY. <p>
	/// 
	/// Valid options are:<p>
	/// 
	/// -I num <br>
	/// The number of iterations to be performed. (default 1)<p>
	/// 
	/// -E num <br>
	/// The exponent for the polynomial kernel. (default 1)<p>
	/// 
	/// -S num <br>
	/// The seed for the random number generator. (default 1)<p>
	/// 
	/// -M num <br>
	/// The maximum number of alterations allowed. (default 10000) <p>
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.17 $ 
	/// </version>
	/// <attribute>  System.ComponentModel.DescriptionAttribute("Implements the voted perceptron algorithm by Freund and Schapire.")  </attribute>
#if !PocketPC	
    [Serializable]
#endif
	public class VotedPerceptron:Classifier
	//implements OptionHandler 
	{
		/// <summary>The maximum number of alterations to the perceptron </summary>
		private int m_MaxK = 10000;
		/// <summary>The number of iterations </summary>
		private int m_NumIterations = 1;
		/// <summary>The exponent </summary>
		private double m_Exponent = 1.0;
		/// <summary>The actual number of alterations </summary>
		private int m_K = 0;
		/// <summary>The training instances added to the perceptron </summary>
		private int[] m_Additions = null;
		/// <summary>Addition or subtraction? </summary>
		private bool[] m_IsAddition = null;
		/// <summary>The weights for each perceptron </summary>
		private int[] m_Weights = null;
		/// <summary>The training instances </summary>
		private Instances m_Train = null;
		/// <summary>Seed used for shuffling the dataset </summary>
		private int m_Seed = 1;
		/// <summary>The filter used to make attributes numeric. </summary>
		private NominalToBinary m_NominalToBinary;
		/// <summary>The filter used to get rid of missing values. </summary>
		private ReplaceMissingValues m_ReplaceMissingValues;


        public override void toXML(TextWriter tw)
        {

        }
		/// <summary> Builds the ensemble of perceptrons.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong during building
		/// </exception>
        /// 
        public override void buildClassifier(string fileName, Instances instances)
        {
        }
		public override void  buildClassifier(Instances insts)
		{
			
			if (insts.checkForStringAttributes())
			{
				throw new Exception("Cannot handle string attributes!");
			}
			if (insts.numClasses() > 2)
			{
				throw new System.Exception("Can only handle two-class datasets!");
			}
			if (insts.classAttribute().Numeric)
			{
				throw new Exception("Can't handle a numeric class!");
			}
			
			// Filter data
			m_Train = new Instances(insts);
			m_Train.deleteWithMissingClass();
			m_ReplaceMissingValues = new ReplaceMissingValues();
			m_ReplaceMissingValues.setInputFormat(m_Train);
			m_Train = Filter.useFilter(m_Train, m_ReplaceMissingValues);
			
			m_NominalToBinary = new NominalToBinary();
			m_NominalToBinary.setInputFormat(m_Train);
			m_Train = Filter.useFilter(m_Train, m_NominalToBinary);
			
			/** Randomize training data */
			//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.util.Random.Random'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
			m_Train.randomize(new System.Random((System.Int32) m_Seed));
			
			/** Make space to store perceptrons */
			m_Additions = new int[m_MaxK + 1];
			m_IsAddition = new bool[m_MaxK + 1];
			m_Weights = new int[m_MaxK + 1];
			
			/** Compute perceptrons */
			m_K = 0;
			for (int it = 0; it < m_NumIterations; it++)
			{
				for (int i = 0; i < m_Train.numInstances(); i++)
				{
					Instance inst = m_Train.instance(i);
					if (!inst.classIsMissing())
					{
						int prediction = makePrediction(m_K, inst);
						//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
						int classValue = (int) inst.classValue();
						if (prediction == classValue)
						{
							m_Weights[m_K]++;
						}
						else
						{
							m_IsAddition[m_K] = (classValue == 1);
							m_Additions[m_K] = i;
							m_K++;
							m_Weights[m_K]++;
						}
						if (m_K == m_MaxK)
						{
							//UPGRADE_NOTE: Labeled break statement was changed to a goto statement. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1012'"
							goto out_brk;
						}
					}
				}
			}
			//UPGRADE_NOTE: Label 'out_brk' was added. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1011'"

out_brk: ;
			
		}
		
		/// <summary> Outputs the distribution for the given output.
		/// 
		/// Pipes output of SVM through sigmoid function.
		/// </summary>
		/// <param name="inst">the instance for which distribution is to be computed
		/// </param>
		/// <returns> the distribution
		/// </returns>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public override double[] distributionForInstance(Instance inst)
		{
			
			// Filter instance
			m_ReplaceMissingValues.input(inst);
			m_ReplaceMissingValues.batchFinished();
			inst = m_ReplaceMissingValues.output();
			
			m_NominalToBinary.input(inst);
			m_NominalToBinary.batchFinished();
			inst = m_NominalToBinary.output();
			
			// Get probabilities
			double output = 0, sumSoFar = 0;
			if (m_K > 0)
			{
				for (int i = 0; i <= m_K; i++)
				{
					if (sumSoFar < 0)
					{
						output -= m_Weights[i];
					}
					else
					{
						output += m_Weights[i];
					}
					if (m_IsAddition[i])
					{
						sumSoFar += innerProduct(m_Train.instance(m_Additions[i]), inst);
					}
					else
					{
						sumSoFar -= innerProduct(m_Train.instance(m_Additions[i]), inst);
					}
				}
			}
			double[] result = new double[2];
			result[1] = 1 / (1 + System.Math.Exp(- output));
			result[0] = 1 - result[1];
			
			return result;
		}
		
		/// <summary> Returns textual description of classifier.</summary>
		public override System.String ToString()
		{
			
			return "VotedPerceptron: Number of perceptrons=" + m_K;
		}
		
		
		
		/// <summary> Get the value of maxK.
		/// 
		/// </summary>
		/// <returns> Value of maxK.
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("The maximum number of alterations to the perceptron.")  </attribute>
		/// <property>   </property>
		public virtual int get_MaxK()
		{
			
			return m_MaxK;
		}
		
		/// <summary> Set the value of maxK.
		/// 
		/// </summary>
		/// <param name="v"> Value to assign to maxK.
		/// </param>
		/// <property>   </property>
		public virtual void  set_MaxK(int v)
		{
			
			m_MaxK = v;
		}
		
		
		
		/// <summary> Get the value of NumIterations.
		/// 
		/// </summary>
		/// <returns> Value of NumIterations.
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Number of iterations to be performed.")  </attribute>
		/// <property>   </property>
		public virtual int get_NumIterations()
		{
			
			return m_NumIterations;
		}
		
		/// <summary> Set the value of NumIterations.
		/// 
		/// </summary>
		/// <param name="v"> Value to assign to NumIterations.
		/// </param>
		/// <property>   </property>
		public virtual void  set_NumIterations(int v)
		{
			
			m_NumIterations = v;
		}
		
		
		/// <summary> Get the value of exponent.
		/// 
		/// </summary>
		/// <returns> Value of exponent.
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Exponent for the polynomial kernel.")  </attribute>
		/// <property>   </property>
		public virtual double get_Exponent()
		{
			
			return m_Exponent;
		}
		
		/// <summary> Set the value of exponent.
		/// 
		/// </summary>
		/// <param name="v"> Value to assign to exponent.
		/// </param>
		/// <property>   </property>
		public virtual void  set_Exponent(double v)
		{
			
			m_Exponent = v;
		}
		
		
		
		/// <summary> Get the value of Seed.
		/// 
		/// </summary>
		/// <returns> Value of Seed.
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Seed for the random number generator.")  </attribute>
		/// <property>   </property>
		public virtual int get_Seed()
		{
			
			return m_Seed;
		}
		
		/// <summary> Set the value of Seed.
		/// 
		/// </summary>
		/// <param name="v"> Value to assign to Seed.
		/// </param>
		/// <property>   </property>
		public virtual void  set_Seed(int v)
		{
			
			m_Seed = v;
		}
		
		/// <summary> Computes the inner product of two instances</summary>
		private double innerProduct(Instance i1, Instance i2)
		{
			
			// we can do a fast dot product
			double result = 0;
			int n1 = i1.numValues(); int n2 = i2.numValues();
			int classIndex = m_Train.classIndex();
			for (int p1 = 0, p2 = 0; p1 < n1 && p2 < n2; )
			{
				int ind1 = i1.index(p1);
				int ind2 = i2.index(p2);
				if (ind1 == ind2)
				{
					if (ind1 != classIndex)
					{
						result += i1.valueSparse(p1) * i2.valueSparse(p2);
					}
					p1++; p2++;
				}
				else if (ind1 > ind2)
				{
					p2++;
				}
				else
				{
					p1++;
				}
			}
			result += 1.0;
			
			if (m_Exponent != 1)
			{
				return System.Math.Pow(result, m_Exponent);
			}
			else
			{
				return result;
			}
		}
		
		/// <summary> Compute a prediction from a perceptron</summary>
		private int makePrediction(int k, Instance inst)
		{
			
			double result = 0;
			for (int i = 0; i < k; i++)
			{
				if (m_IsAddition[i])
				{
					result += innerProduct(m_Train.instance(m_Additions[i]), inst);
				}
				else
				{
					result -= innerProduct(m_Train.instance(m_Additions[i]), inst);
				}
			}
			if (result < 0)
			{
				return 0;
			}
			else
			{
				return 1;
			}
		}
		//UPGRADE_TODO: The following method was automatically generated and it must be implemented in order to preserve the class logic. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1232'"
		override public System.Object Clone()
		{
			return null;
		}
	}
}