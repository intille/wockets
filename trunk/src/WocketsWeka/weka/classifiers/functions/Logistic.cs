/*
*    Logistic.java
*    Copyright (C) 2003 Xin Xu
*/
using System;
using weka.classifiers;
using weka.core;
using weka.filters;
//UPGRADE_TODO: The package 'weka.filters.unsupervised.attribute' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using weka.filters.unsupervised.attribute;
using System.IO;
namespace weka.classifiers.functions
{
	
	/// <summary> Second implementation for building and using a multinomial logistic
	/// regression model with a ridge estimator.  <p>
	/// 
	/// There are some modifications, however, compared to the paper of le
	/// Cessie and van Houwelingen(1992): <br>
	/// 
	/// If there are k classes for n instances with m attributes, the
	/// parameter matrix B to be calculated will be an m*(k-1) matrix.<br>
	/// 
	/// The probability for class j except the last class is <br>
	/// Pj(Xi) = exp(XiBj)/((sum[j=1..(k-1)]exp(Xi*Bj))+1) <br>
	/// The last class has probability <br>
	/// 1-(sum[j=1..(k-1)]Pj(Xi)) = 1/((sum[j=1..(k-1)]exp(Xi*Bj))+1) <br>
	/// 
	/// The (negative) multinomial log-likelihood is thus: <br>
	/// L = -sum[i=1..n]{
	/// sum[j=1..(k-1)](Yij * ln(Pj(Xi))) +
	/// (1 - (sum[j=1..(k-1)]Yij)) * ln(1 - sum[j=1..(k-1)]Pj(Xi))
	/// } + ridge * (B^2) <br>
	/// 
	/// In order to find the matrix B for which L is minimised, a
	/// Quasi-Newton Method is used to search for the optimized values of
	/// the m*(k-1) variables.  Note that before we use the optimization
	/// procedure, we "squeeze" the matrix B into a m*(k-1) vector.  For
	/// details of the optimization procedure, please check
	/// weka.core.Optimization class. <p>
	/// 
	/// Although original Logistic Regression does not deal with instance
	/// weights, we modify the algorithm a little bit to handle the
	/// instance weights. <p>
	/// 
	/// Reference: le Cessie, S. and van Houwelingen, J.C. (1992). <i>
	/// Ridge Estimators in Logistic Regression.</i> Applied Statistics,
	/// Vol. 41, No. 1, pp. 191-201. <p>
	/// 
	/// Missing values are replaced using a ReplaceMissingValuesFilter, and
	/// nominal attributes are transformed into numeric attributes using a
	/// NominalToBinaryFilter.<p>
	/// 
	/// Valid options are:<p>
	/// 
	/// -D <br>
	/// Turn on debugging output.<p>
	/// 
	/// -R <ridge> <br>
	/// Set the ridge parameter for the log-likelihood.<p>
	/// 
	/// -M <number of iterations> <br> Set the maximum number of iterations
	/// (default -1, iterates until convergence).<p>
	/// 
	/// </summary>
	/// <author>  Xin Xu (xx5@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.32 $ 
	/// </version>
	/// <attribute>  System.ComponentModel.DescriptionAttribute("Second implementation for building and using a multinomial logistic regression model with a ridge estimator.")  </attribute>
#if !PocketPC
    [Serializable]
#endif
	public class Logistic:Classifier, WeightedInstancesHandler
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets whether debugging output will be printed.
		/// 
		/// </summary>
		/// <returns> true if debugging output will be printed
		/// </returns>
		/// <summary> Sets whether debugging output will be printed.
		/// 
		/// </summary>
		/// <param name="debug">true if debugging output should be printed
		/// </param>
		override public bool Debug
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
		/// <summary>The coefficients (optimized parameters) of the model </summary>
		protected internal double[][] m_Par;
		/// <summary>The data saved as a matrix </summary>
		protected internal double[][] m_Data;
		/// <summary>The number of attributes in the model </summary>
		protected internal int m_NumPredictors;
		/// <summary>The index of the class attribute </summary>
		protected internal int m_ClassIndex;
		/// <summary>The number of the class labels </summary>
		protected internal int m_NumClasses;
		/// <summary>The ridge parameter. </summary>
		protected internal double m_Ridge = 1e-8;
		/* An attribute filter */
		private RemoveUseless m_AttFilter;
		/// <summary>The filter used to make attributes numeric. </summary>
		private NominalToBinary m_NominalToBinary;
		/// <summary>The filter used to get rid of missing values. </summary>
		private ReplaceMissingValues m_ReplaceMissingValues;
		/// <summary>Debugging output </summary>
		new protected internal bool m_Debug;
		/// <summary>Log-likelihood of the searched model </summary>
		protected internal double m_LL;
		/// <summary>The maximum number of iterations. </summary>
		private int m_MaxIts = - 1;
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public override System.String debugTipText()
		{
			return "Output debug information to the console.";
		}
		
		
		/// <summary> Sets the ridge in the log-likelihood.
		/// 
		/// </summary>
		/// <param name="ridge">the ridge
		/// </param>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Set the Ridge value in the log-likelihood.")  </attribute>
		/// <property>   </property>
		public virtual void  set_Ridge(double ridge)
		{
			m_Ridge = ridge;
		}
		
		/// <summary> Gets the ridge in the log-likelihood.
		/// 
		/// </summary>
		/// <returns> the ridge
		/// </returns>
		/// <property>   </property>
		public virtual double get_Ridge()
		{
			return m_Ridge;
		}
		
		
		/// <summary> Get the value of MaxIts.
		/// 
		/// </summary>
		/// <returns> Value of MaxIts.
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Maximum number of iterations to perform.")  </attribute>
		/// <property>   </property>
		public virtual int get_MaxIts()
		{
			
			return m_MaxIts;
		}
		
		/// <summary> Set the value of MaxIts.
		/// 
		/// </summary>
		/// <param name="newMaxIts">Value to assign to MaxIts.
		/// </param>
		/// <property>   </property>
		public virtual void  set_MaxIts(int newMaxIts)
		{
			
			m_MaxIts = newMaxIts;
		}
		
		//UPGRADE_NOTE: Field 'EnclosingInstance' was added to class 'OptEng' to access its enclosing instance. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1019'"
		private class OptEng: Optimization
		{
            // Weights of instances in the data
            private double[] weights;
            // Class labels of instances
            private int[] cls;
            private Logistic Enclosing_Instance;

            public OptEng(Logistic Enclosing_Instance)
            {
                this.Enclosing_Instance = Enclosing_Instance;
            }
			virtual public double[] Weights
			{
				/* Set the weights of instances
				* @param d the weights to be set
				*/
				
				set
				{
					weights = value;
				}
				
			}
			virtual public int[] ClassLabels
			{
				/* Set the class labels of instances
				* @param d the class labels to be set
				*/
				
				set
				{
					cls = value;
				}
				
			}


			
			/// <summary> Evaluate objective function</summary>
			/// <param name="x">the current values of variables
			/// </param>
			/// <returns> the value of the objective function 
			/// </returns>
			protected override double objectiveFunction(double[] x)
			{
				double nll = 0; // -LogLikelihood
				int dim = Enclosing_Instance.m_NumPredictors + 1; // Number of variables per class
				
				for (int i = 0; i < cls.Length; i++)
				{
					// ith instance
					
					double[] exp = new double[Enclosing_Instance.m_NumClasses - 1];
					int index;
					for (int offset = 0; offset < Enclosing_Instance.m_NumClasses - 1; offset++)
					{
						index = offset * dim;
						for (int j = 0; j < dim; j++)
							exp[offset] += Enclosing_Instance.m_Data[i][j] * x[index + j];
					}
					double max = exp[Utils.maxIndex(exp)];
					double denom = System.Math.Exp(- max);
					double num;
					if (cls[i] == Enclosing_Instance.m_NumClasses - 1)
					{
						// Class of this instance
						num = - max;
					}
					else
					{
						num = exp[cls[i]] - max;
					}
					for (int offset = 0; offset < Enclosing_Instance.m_NumClasses - 1; offset++)
					{
						denom += System.Math.Exp(exp[offset] - max);
					}
					
					nll -= weights[i] * (num - System.Math.Log(denom)); // Weighted NLL
				}
				
				// Ridge: note that intercepts NOT included
				for (int offset = 0; offset < Enclosing_Instance.m_NumClasses - 1; offset++)
				{
					for (int r = 1; r < dim; r++)
						nll += Enclosing_Instance.m_Ridge * x[offset * dim + r] * x[offset * dim + r];
				}
				
				return nll;
			}
			
			/// <summary> Evaluate Jacobian vector</summary>
			/// <param name="x">the current values of variables
			/// </param>
			/// <returns> the gradient vector 
			/// </returns>
            protected override double[] evaluateGradient(double[] x)
			{
				double[] grad = new double[x.Length];
				int dim = Enclosing_Instance.m_NumPredictors + 1; // Number of variables per class
				
				for (int i = 0; i < cls.Length; i++)
				{
					// ith instance
					double[] num = new double[Enclosing_Instance.m_NumClasses - 1]; // numerator of [-log(1+sum(exp))]'
					int index;
					for (int offset = 0; offset < Enclosing_Instance.m_NumClasses - 1; offset++)
					{
						// Which part of x
						double exp = 0.0;
						index = offset * dim;
						for (int j = 0; j < dim; j++)
							exp += Enclosing_Instance.m_Data[i][j] * x[index + j];
						num[offset] = exp;
					}
					
					double max = num[Utils.maxIndex(num)];
					double denom = System.Math.Exp(- max); // Denominator of [-log(1+sum(exp))]'
					for (int offset = 0; offset < Enclosing_Instance.m_NumClasses - 1; offset++)
					{
						num[offset] = System.Math.Exp(num[offset] - max);
						denom += num[offset];
					}
					Utils.normalize(num, denom);
					
					// Update denominator of the gradient of -log(Posterior)
					double firstTerm;
					for (int offset = 0; offset < Enclosing_Instance.m_NumClasses - 1; offset++)
					{
						// Which part of x
						index = offset * dim;
						firstTerm = weights[i] * num[offset];
						for (int q = 0; q < dim; q++)
						{
							grad[index + q] += firstTerm * Enclosing_Instance.m_Data[i][q];
						}
					}
					
					if (cls[i] != Enclosing_Instance.m_NumClasses - 1)
					{
						// Not the last class
						for (int p = 0; p < dim; p++)
						{
							grad[cls[i] * dim + p] -= weights[i] * Enclosing_Instance.m_Data[i][p];
						}
					}
				}
				
				// Ridge: note that intercepts NOT included
				for (int offset = 0; offset < Enclosing_Instance.m_NumClasses - 1; offset++)
				{
					for (int r = 1; r < dim; r++)
						grad[offset * dim + r] += 2 * Enclosing_Instance.m_Ridge * x[offset * dim + r];
				}
				
				return grad;
			}
		}

        public override void toXML(TextWriter tw)
        {     
        }

        public override void  buildClassifier(string fileName, Instances instances)
        {
        }
		/// <summary> Builds the classifier
		/// 
		/// </summary>
		/// <param name="train">the training data to be used for generating the
		/// boosted classifier.
		/// </param>
		/// <exception cref="Exception">if the classifier could not be built successfully
		/// </exception>
		public override void  buildClassifier(Instances train)
		{
			if (train.classAttribute().type() != weka.core.Attribute.NOMINAL)
			{
				throw new Exception("Class attribute must be nominal.");
			}
			if (train.checkForStringAttributes())
			{
				throw new Exception("Can't handle string attributes!");
			}
			train = new Instances(train);
			train.deleteWithMissingClass();
			if (train.numInstances() == 0)
			{
				throw new System.ArgumentException("No train instances without missing class value!");
			}
			
			// Replace missing values	
			m_ReplaceMissingValues = new ReplaceMissingValues();
			m_ReplaceMissingValues.setInputFormat(train);
			train = Filter.useFilter(train, m_ReplaceMissingValues);
			
			// Remove useless attributes
			m_AttFilter = new RemoveUseless();
			m_AttFilter.setInputFormat(train);
			train = Filter.useFilter(train, m_AttFilter);
			
			// Transform attributes
			m_NominalToBinary = new NominalToBinary();
			m_NominalToBinary.setInputFormat(train);
			train = Filter.useFilter(train, m_NominalToBinary);
			
			// Extract data
			m_ClassIndex = train.classIndex();
			m_NumClasses = train.numClasses();
			
			int nK = m_NumClasses - 1; // Only K-1 class labels needed 
			int nR = m_NumPredictors = train.numAttributes() - 1;
			int nC = train.numInstances();
			
			m_Data = new double[nC][];
			for (int i = 0; i < nC; i++)
			{
				m_Data[i] = new double[nR + 1];
			} // Data values
			int[] Y = new int[nC]; // Class labels
			double[] xMean = new double[nR + 1]; // Attribute means
			double[] xSD = new double[nR + 1]; // Attribute stddev's
			double[] sY = new double[nK + 1]; // Number of classes
			double[] weights = new double[nC]; // Weights of instances
			double totWeights = 0; // Total weights of the instances
			m_Par = new double[nR + 1][];
			for (int i2 = 0; i2 < nR + 1; i2++)
			{
				m_Par[i2] = new double[nK];
			} // Optimized parameter values
			
			if (m_Debug)
			{
				System.Console.Out.WriteLine("Extracting data...");
			}
			
			for (int i = 0; i < nC; i++)
			{
				// initialize X[][]
				Instance current = train.instance(i);
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				Y[i] = (int) current.classValue(); // Class value starts from 0
				weights[i] = current.weight(); // Dealing with weights
				totWeights += weights[i];
				
				m_Data[i][0] = 1;
				int j = 1;
				for (int k = 0; k <= nR; k++)
				{
					if (k != m_ClassIndex)
					{
						double x = current.value_Renamed(k);
						m_Data[i][j] = x;
						xMean[j] += weights[i] * x;
						xSD[j] += weights[i] * x * x;
						j++;
					}
				}
				
				// Class count
				sY[Y[i]]++;
			}
			
			if ((totWeights <= 1) && (nC > 1))
				throw new System.Exception("Sum of weights of instances less than 1, please reweight!");
			
			xMean[0] = 0; xSD[0] = 1;
			for (int j = 1; j <= nR; j++)
			{
				xMean[j] = xMean[j] / totWeights;
				if (totWeights > 1)
					xSD[j] = System.Math.Sqrt(System.Math.Abs(xSD[j] - totWeights * xMean[j] * xMean[j]) / (totWeights - 1));
				else
					xSD[j] = 0;
			}
			
			if (m_Debug)
			{
				// Output stats about input data
				System.Console.Out.WriteLine("Descriptives...");
				for (int m = 0; m <= nK; m++)
					System.Console.Out.WriteLine(sY[m] + " cases have class " + m);
				System.Console.Out.WriteLine("\n Variable     Avg       SD    ");
				for (int j = 1; j <= nR; j++)
					System.Console.Out.WriteLine(Utils.doubleToString(j, 8, 4) + Utils.doubleToString(xMean[j], 10, 4) + Utils.doubleToString(xSD[j], 10, 4));
			}
			
			// Normalise input data 
			for (int i = 0; i < nC; i++)
			{
				for (int j = 0; j <= nR; j++)
				{
					if (xSD[j] != 0)
					{
						m_Data[i][j] = (m_Data[i][j] - xMean[j]) / xSD[j];
					}
				}
			}
			
			if (m_Debug)
			{
				System.Console.Out.WriteLine("\nIteration History...");
			}
			
			double[] x2 = new double[(nR + 1) * nK];
			double[][] b = new double[2][];
			for (int i3 = 0; i3 < 2; i3++)
			{
				b[i3] = new double[x2.Length];
			} // Boundary constraints, N/A here
			
			// Initialize
			for (int p = 0; p < nK; p++)
			{
				int offset = p * (nR + 1);
				x2[offset] = System.Math.Log(sY[p] + 1.0) - System.Math.Log(sY[nK] + 1.0); // Null model
				b[0][offset] = System.Double.NaN;
				b[1][offset] = System.Double.NaN;
				for (int q = 1; q <= nR; q++)
				{
					x2[offset + q] = 0.0;
					b[0][offset + q] = System.Double.NaN;
					b[1][offset + q] = System.Double.NaN;
				}
			}
			
			OptEng opt = new OptEng(this);
			opt.Debug = m_Debug;
			opt.Weights = weights;
			opt.ClassLabels = Y;
			
			if (m_MaxIts == - 1)
			{
				// Search until convergence
				x2 = opt.findArgmin(x2, b);
				while (x2 == null)
				{
					x2 = opt.VarbValues;
					if (m_Debug)
						System.Console.Out.WriteLine("200 iterations finished, not enough!");
					x2 = opt.findArgmin(x2, b);
				}
				if (m_Debug)
					System.Console.Out.WriteLine(" -------------<Converged>--------------");
			}
			else
			{
				opt.MaxIteration=m_MaxIts;
				x2 = opt.findArgmin(x2, b);
				if (x2 == null)
				// Not enough, but use the current value
					x2 = opt.VarbValues;
			}
			
			m_LL = - opt.MinFunction; // Log-likelihood
			
			// Don't need data matrix anymore
			m_Data = null;
			
			// Convert coefficients back to non-normalized attribute units
			for (int i = 0; i < nK; i++)
			{
				m_Par[0][i] = x2[i * (nR + 1)];
				for (int j = 1; j <= nR; j++)
				{
					m_Par[j][i] = x2[i * (nR + 1) + j];
					if (xSD[j] != 0)
					{
						m_Par[j][i] /= xSD[j];
						m_Par[0][i] -= m_Par[j][i] * xMean[j];
					}
				}
			}
		}
		
		/// <summary> Computes the distribution for a given instance
		/// 
		/// </summary>
		/// <param name="instance">the instance for which distribution is computed
		/// </param>
		/// <returns> the distribution
		/// </returns>
		/// <exception cref="Exception">if the distribution can't be computed successfully
		/// </exception>
		public override double[] distributionForInstance(Instance instance)
		{
			
			m_ReplaceMissingValues.input(instance);
			instance = m_ReplaceMissingValues.output();
			m_AttFilter.input(instance);
			instance = m_AttFilter.output();
			m_NominalToBinary.input(instance);
			instance = m_NominalToBinary.output();
			
			// Extract the predictor columns into an array
			double[] instDat = new double[m_NumPredictors + 1];
			int j = 1;
			instDat[0] = 1;
			for (int k = 0; k <= m_NumPredictors; k++)
			{
				if (k != m_ClassIndex)
				{
					instDat[j++] = instance.value_Renamed(k);
				}
			}
			
			double[] distribution = evaluateProbability(instDat);
			return distribution;
		}
		
		/// <summary> Compute the posterior distribution using optimized parameter values
		/// and the testing instance.
		/// </summary>
		/// <param name="data">the testing instance
		/// </param>
		/// <returns> the posterior probability distribution
		/// </returns>
		private double[] evaluateProbability(double[] data)
		{
			double[] prob = new double[m_NumClasses], v = new double[m_NumClasses];
			
			// Log-posterior before normalizing
			for (int j = 0; j < m_NumClasses - 1; j++)
			{
				for (int k = 0; k <= m_NumPredictors; k++)
				{
					v[j] += m_Par[k][j] * data[k];
				}
			}
			v[m_NumClasses - 1] = 0;
			
			// Do so to avoid scaling problems
			for (int m = 0; m < m_NumClasses; m++)
			{
				double sum = 0;
				for (int n = 0; n < m_NumClasses - 1; n++)
					sum += System.Math.Exp(v[n] - v[m]);
				prob[m] = 1 / (sum + System.Math.Exp(- v[m]));
			}
			
			return prob;
		}
		
		/// <summary> Gets a string describing the classifier.
		/// 
		/// </summary>
		/// <returns> a string describing the classifer built.
		/// </returns>
		public override System.String ToString()
		{
			
			//double CSq;
			//int df = m_NumPredictors;
			System.String result = "Logistic Regression with ridge parameter of " + m_Ridge;
			if (m_Par == null)
			{
				return result + ": No model built yet.";
			}
			
			result += ("\nCoefficients...\n" + "Variable      Coeff.\n");
			for (int j = 1; j <= m_NumPredictors; j++)
			{
				result += Utils.doubleToString(j, 8, 0);
				for (int k = 0; k < m_NumClasses - 1; k++)
					result += (" " + Utils.doubleToString(m_Par[j][k], 12, 4));
				result += "\n";
			}
			
			result += "Intercept ";
			for (int k = 0; k < m_NumClasses - 1; k++)
				result += (" " + Utils.doubleToString(m_Par[0][k], 10, 4));
			result += "\n";
			
			result += ("\nOdds Ratios...\n" + "Variable         O.R.\n");
			for (int j = 1; j <= m_NumPredictors; j++)
			{
				result += Utils.doubleToString(j, 8, 0);
				for (int k = 0; k < m_NumClasses - 1; k++)
				{
					double ORc = System.Math.Exp(m_Par[j][k]);
					result += (" " + ((ORc > 1e10)?"" + ORc:Utils.doubleToString(ORc, 12, 4)));
				}
				result += "\n";
			}
			return result;
		}
		//UPGRADE_TODO: The following method was automatically generated and it must be implemented in order to preserve the class logic. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1232'"
		override public System.Object Clone()
		{
			return null;
		}
	}
}