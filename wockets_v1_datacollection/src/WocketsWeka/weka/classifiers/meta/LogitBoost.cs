/*    LogitBoost.java
*    Copyright (C) 1999, 2002 Len Trigg, Eibe Frank
*/
using System;
using weka.classifiers;
//UPGRADE_TODO: The type 'weka.classifiers.trees.DecisionStump' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using DecisionStump = weka.classifiers.trees.DecisionStump;
using weka.core;
using System.IO;
namespace weka.classifiers.meta
{
	
	/// <summary> Class for performing additive logistic regression..
	/// This class performs classification using a regression scheme as the 
	/// base learner, and can handle multi-class problems.  For more
	/// information, see<p>
	/// 
	/// Friedman, J., T. Hastie and R. Tibshirani (1998) <i>Additive Logistic
	/// Regression: a Statistical View of Boosting</i> 
	/// <a href="http://www-stat.stanford.edu/~jhf/ftp/boost.ps">download 
	/// postscript</a>. <p>
	/// 
	/// Valid options are:<p>
	/// 
	/// -D <br>
	/// Turn on debugging output.<p>
	/// 
	/// -W classname <br>
	/// Specify the full class name of a weak learner as the basis for 
	/// boosting (required).<p>
	/// 
	/// -I num <br>
	/// Set the number of boost iterations (default 10). <p>
	/// 
	/// -Q <br>
	/// Use resampling instead of reweighting.<p>
	/// 
	/// -S seed <br>
	/// Random number seed for resampling (default 1).<p>
	/// 
	/// -P num <br>
	/// Set the percentage of weight mass used to build classifiers
	/// (default 100). <p>
	/// 
	/// -F num <br>
	/// Set number of folds for the internal cross-validation
	/// (default 0 -- no cross-validation). <p>
	/// 
	/// -R num <br>
	/// Set number of runs for the internal cross-validation
	/// (default 1). <p>
	/// 
	/// -L num <br> 
	/// Set the threshold for the improvement of the
	/// average loglikelihood (default -Double.MAX_VALUE). <p>
	/// 
	/// -H num <br> 
	/// Set the value of the shrinkage parameter (default 1). <p>
	/// 
	/// Options after -- are passed to the designated learner.<p>
	/// 
	/// </summary>
	/// <author>  Len Trigg (trigg@cs.waikato.ac.nz)
	/// </author>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.33 $ 
	/// </version>
	/// <attribute>  System.ComponentModel.DescriptionAttribute("Class for performing additive logistic regression. This class performs classification using a regression scheme as the base learner, and can handle multi-class problems.")  </attribute>
	public class LogitBoost:RandomizableIteratedSingleClassifierEnhancer, Sourcable, WeightedInstancesHandler
	{
		/// <summary>Array for storing the generated base classifiers. 
		/// Note: we are hiding the variable from IteratedSingleClassifierEnhancer
		/// </summary>
		protected internal Classifier[][] m_Classifiers;
		/// <summary>The number of classes </summary>
		protected internal int m_NumClasses;
		/// <summary>The number of successfully generated base classifiers. </summary>
		protected internal int m_NumGenerated;
		/// <summary>The number of folds for the internal cross-validation. </summary>
		protected internal int m_NumFolds = 0;
		/// <summary>The number of runs for the internal cross-validation. </summary>
		protected internal int m_NumRuns = 1;
		/// <summary>Weight thresholding. The percentage of weight mass used in training </summary>
		protected internal int m_WeightThreshold = 100;
		/// <summary>A threshold for responses (Friedman suggests between 2 and 4) </summary>
		protected internal const double Z_MAX = 3;
		/// <summary>Dummy dataset with a numeric class </summary>
		protected internal Instances m_NumericClassData;
		/// <summary>The actual class attribute (for getting class names) </summary>
		protected internal weka.core.Attribute m_ClassAttribute;
		/// <summary>Use boosting with reweighting? </summary>
		protected internal bool m_UseResampling;
		/// <summary>The threshold on the improvement of the likelihood </summary>
		//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
		protected internal double m_Precision = - System.Double.MaxValue;
		/// <summary>The value of the shrinkage parameter </summary>
		protected internal double m_Shrinkage = 1;
		/// <summary>The random number generator used </summary>
		protected internal System.Random m_RandomInstance = null;
		/// <summary>The value by which the actual target value for the
		/// true class is offset. 
		/// </summary>
		protected internal double m_Offset = 0.0;

        public override void  toXML(TextWriter tw)
        {
 
        }

		/// <summary> Constructor.</summary>
		public LogitBoost()
		{
			
			m_Classifier = new weka.classifiers.trees.DecisionStump();
		}
		
		/// <summary> String describing default classifier.</summary>
		protected internal virtual System.String defaultClassifierString()
		{
			
			return "weka.classifiers.trees.DecisionStump";
		}
		
		/// <summary> Select only instances with weights that contribute to 
		/// the specified quantile of the weight distribution
		/// 
		/// </summary>
		/// <param name="data">the input instances
		/// </param>
		/// <param name="quantile">the specified quantile eg 0.9 to select 
		/// 90% of the weight mass
		/// </param>
		/// <returns> the selected instances
		/// </returns>
		protected internal virtual Instances selectWeightQuantile(Instances data, double quantile)
		{
			
			int numInstances = data.numInstances();
			Instances trainData = new Instances(data, numInstances);
			double[] weights = new double[numInstances];
			
			double sumOfWeights = 0;
			for (int i = 0; i < numInstances; i++)
			{
				weights[i] = data.instance(i).weight();
				sumOfWeights += weights[i];
			}
			double weightMassToSelect = sumOfWeights * quantile;
			int[] sortedIndices = Utils.sort(weights);
			
			// Select the instances
			sumOfWeights = 0;
			for (int i = numInstances - 1; i >= 0; i--)
			{
				Instance instance = (Instance) data.instance(sortedIndices[i]).copy();
				trainData.add(instance);
				sumOfWeights += weights[sortedIndices[i]];
				if ((sumOfWeights > weightMassToSelect) && (i > 0) && (weights[sortedIndices[i]] != weights[sortedIndices[i - 1]]))
				{
					break;
				}
			}
			if (m_Debug)
			{
				System.Console.Error.WriteLine("Selected " + trainData.numInstances() + " out of " + numInstances);
			}
			return trainData;
		}
		
		
		
		/// <summary> Get the value of Shrinkage.
		/// 
		/// </summary>
		/// <returns> Value of Shrinkage.
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Shrinkage parameter (use small value like 0.1 to reduce overfitting).")  </attribute>
		/// <property>   </property>
		public virtual double get_Shrinkage()
		{
			
			return m_Shrinkage;
		}
		
		/// <summary> Set the value of Shrinkage.
		/// 
		/// </summary>
		/// <param name="newShrinkage">Value to assign to Shrinkage.
		/// </param>
		/// <property>   </property>
		public virtual void  set_Shrinkage(double newShrinkage)
		{
			
			m_Shrinkage = newShrinkage;
		}
		
		
		
		/// <summary> Get the value of Precision.
		/// 
		/// </summary>
		/// <returns> Value of Precision.
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Threshold on improvement in likelihood.")  </attribute>
		/// <property>   </property>
		public virtual double get_LikelihoodThreshold()
		{
			
			return m_Precision;
		}
		
		/// <summary> Set the value of Precision.
		/// 
		/// </summary>
		/// <param name="newPrecision">Value to assign to Precision.
		/// </param>
		/// <property>   </property>
		public virtual void  set_LikelihoodThreshold(double newPrecision)
		{
			
			m_Precision = newPrecision;
		}
		
		
		
		/// <summary> Get the value of NumRuns.
		/// 
		/// </summary>
		/// <returns> Value of NumRuns.
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Number of runs for internal cross-validation.")  </attribute>
		/// <property>   </property>
		public virtual int get_NumRuns()
		{
			
			return m_NumRuns;
		}
		
		/// <summary> Set the value of NumRuns.
		/// 
		/// </summary>
		/// <param name="newNumRuns">Value to assign to NumRuns.
		/// </param>
		/// <property>   </property>
		public virtual void  set_NumRuns(int newNumRuns)
		{
			
			m_NumRuns = newNumRuns;
		}
		
		
		/// <summary> Get the value of NumFolds.
		/// 
		/// </summary>
		/// <returns> Value of NumFolds.
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Number of folds for internal cross-validation (default 0 means no cross-validation is performed).")  </attribute>
		/// <property>   </property>
		public virtual int get_NumFolds()
		{
			
			return m_NumFolds;
		}
		
		/// <summary> Set the value of NumFolds.
		/// 
		/// </summary>
		/// <param name="newNumFolds">Value to assign to NumFolds.
		/// </param>
		/// <property>   </property>
		public virtual void  set_NumFolds(int newNumFolds)
		{
			
			m_NumFolds = newNumFolds;
		}
		
		
		
		/// <summary> Set resampling mode
		/// 
		/// </summary>
		/// <param name="resampling">true if resampling should be done
		/// </param>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Whether resampling is used instead of reweighting.")  </attribute>
		/// <property>   </property>
		public virtual void  set_UseResampling(bool r)
		{
			
			m_UseResampling = r;
		}
		
		/// <summary> Get whether resampling is turned on
		/// 
		/// </summary>
		/// <returns> true if resampling output is on
		/// </returns>
		/// <property>   </property>
		public virtual bool get_UseResampling()
		{
			
			return m_UseResampling;
		}
		
		
		
		/// <summary> Set weight thresholding
		/// 
		/// </summary>
		/// <param name="thresholding">the percentage of weight mass used for training
		/// </param>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Weight threshold for weight pruning (reduce to 90 for speeding up learning process).")  </attribute>
		/// <property>   </property>
		public virtual void  set_WeightThreshold(int threshold)
		{
			
			m_WeightThreshold = threshold;
		}
		
		/// <summary> Get the degree of weight thresholding
		/// 
		/// </summary>
		/// <returns> the percentage of weight mass used for training
		/// </returns>
		/// <property>   </property>
		public virtual int get_WeightThreshold()
		{
			
			return m_WeightThreshold;
		}


        public override void buildClassifier(string fileName, Instances instances)
        {
        }
		
		/// <summary> Builds the boosted classifier</summary>
		public virtual void  buildClassifier(Instances data)
		{
			m_RandomInstance = new Random(m_Seed);
			Instances boostData;
			int classIndex = data.classIndex();
			
			if (data.classAttribute().Numeric)
			{
				throw new Exception("LogitBoost can't handle a numeric class!");
			}
			if (m_Classifier == null)
			{
				throw new System.Exception("A base classifier has not been specified!");
			}
			
			if (!(m_Classifier is WeightedInstancesHandler) && !m_UseResampling)
			{
				m_UseResampling = true;
			}
			if (data.checkForStringAttributes())
			{
				throw new Exception("Cannot handle string attributes!");
			}
			if (m_Debug)
			{
				System.Console.Error.WriteLine("Creating copy of the training data");
			}
			
			m_NumClasses = data.numClasses();
			m_ClassAttribute = data.classAttribute();
			
			// Create a copy of the data 
			data = new Instances(data);
			data.deleteWithMissingClass();
			
			// Create the base classifiers
			if (m_Debug)
			{
				System.Console.Error.WriteLine("Creating base classifiers");
			}
			m_Classifiers = new Classifier[m_NumClasses][];
			for (int j = 0; j < m_NumClasses; j++)
			{
				m_Classifiers[j] = Classifier.makeCopies(m_Classifier, this.NumIterations);
			}
			
			// Do we want to select the appropriate number of iterations
			// using cross-validation?
			int bestNumIterations = this.NumIterations;
			if (m_NumFolds > 1)
			{
				if (m_Debug)
				{
					System.Console.Error.WriteLine("Processing first fold.");
				}
				
				// Array for storing the results
				double[] results = new double[this.NumIterations];
				
				// Iterate throught the cv-runs
				for (int r = 0; r < m_NumRuns; r++)
				{
					
					// Stratify the data
					data.randomize(m_RandomInstance);
					data.stratify(m_NumFolds);
					
					// Perform the cross-validation
					for (int i = 0; i < m_NumFolds; i++)
					{
						
						// Get train and test folds
						Instances train = data.trainCV(m_NumFolds, i, m_RandomInstance);
						Instances test = data.testCV(m_NumFolds, i);
						
						// Make class numeric
						Instances trainN = new Instances(train);
						trainN.ClassIndex = - 1;
						trainN.deleteAttributeAt(classIndex);
						trainN.insertAttributeAt(new weka.core.Attribute("'pseudo class'"), classIndex);
						trainN.ClassIndex = classIndex;
						m_NumericClassData = new Instances(trainN, 0);
						
						// Get class values
						int numInstances = train.numInstances();
						double[][] tmpArray = new double[numInstances][];
						for (int i2 = 0; i2 < numInstances; i2++)
						{
							tmpArray[i2] = new double[m_NumClasses];
						}
						double[][] trainFs = tmpArray;
						double[][] tmpArray2 = new double[numInstances][];
						for (int i3 = 0; i3 < numInstances; i3++)
						{
							tmpArray2[i3] = new double[m_NumClasses];
						}
						double[][] trainYs = tmpArray2;
						for (int j = 0; j < m_NumClasses; j++)
						{
							for (int k = 0; k < numInstances; k++)
							{
								trainYs[k][j] = (train.instance(k).classValue() == j)?1.0 - m_Offset:0.0 + (m_Offset / (double) m_NumClasses);
							}
						}
						
						// Perform iterations
						double[][] probs = initialProbs(numInstances);
						m_NumGenerated = 0;
						double sumOfWeights = train.sumOfWeights();
						for (int j = 0; j < this.NumIterations; j++)
						{
							performIteration(trainYs, trainFs, probs, trainN, sumOfWeights);
							Evaluation eval = new Evaluation(train);
							eval.evaluateModel(this, test);
							results[j] += eval.correct();
						}
					}
				}
				
				// Find the number of iterations with the lowest error
				//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
				double bestResult = - System.Double.MaxValue;
				for (int j = 0; j < this.NumIterations; j++)
				{
					if (results[j] > bestResult)
					{
						bestResult = results[j];
						bestNumIterations = j;
					}
				}
				if (m_Debug)
				{
					System.Console.Error.WriteLine("Best result for " + bestNumIterations + " iterations: " + bestResult);
				}
			}
			
			// Build classifier on all the data
			int numInstances2 = data.numInstances();
			double[][] trainFs2 = new double[numInstances2][];
			for (int i4 = 0; i4 < numInstances2; i4++)
			{
				trainFs2[i4] = new double[m_NumClasses];
			}
			double[][] trainYs2 = new double[numInstances2][];
			for (int i5 = 0; i5 < numInstances2; i5++)
			{
				trainYs2[i5] = new double[m_NumClasses];
			}
			for (int j = 0; j < m_NumClasses; j++)
			{
				for (int i = 0, k = 0; i < numInstances2; i++, k++)
				{
					trainYs2[i][j] = (data.instance(k).classValue() == j)?1.0 - m_Offset:0.0 + (m_Offset / (double) m_NumClasses);
				}
			}
			
			// Make class numeric
			data.ClassIndex = - 1;
			data.deleteAttributeAt(classIndex);
			data.insertAttributeAt(new weka.core.Attribute("'pseudo class'"), classIndex);
			data.ClassIndex = classIndex;
			m_NumericClassData = new Instances(data, 0);
			
			// Perform iterations
			double[][] probs2 = initialProbs(numInstances2);
            double logLikelihood = CalculateLogLikelihood(trainYs2, probs2);
			m_NumGenerated = 0;
			if (m_Debug)
			{
				System.Console.Error.WriteLine("Avg. log-likelihood: " + logLikelihood);
			}
			double sumOfWeights2 = data.sumOfWeights();
			for (int j = 0; j < bestNumIterations; j++)
			{
				double previousLoglikelihood = logLikelihood;
				performIteration(trainYs2, trainFs2, probs2, data, sumOfWeights2);
                logLikelihood = CalculateLogLikelihood(trainYs2, probs2);
				if (m_Debug)
				{
					System.Console.Error.WriteLine("Avg. log-likelihood: " + logLikelihood);
				}
				if (System.Math.Abs(previousLoglikelihood - logLikelihood) < m_Precision)
				{
					return ;
				}
			}
		}
		
		/// <summary> Gets the intial class probabilities.</summary>
		private double[][] initialProbs(int numInstances)
		{
			
			double[][] probs = new double[numInstances][];
			for (int i = 0; i < numInstances; i++)
			{
				probs[i] = new double[m_NumClasses];
			}
			for (int i = 0; i < numInstances; i++)
			{
				for (int j = 0; j < m_NumClasses; j++)
				{
					probs[i][j] = 1.0 / m_NumClasses;
				}
			}
			return probs;
		}
		
		/// <summary> Computes loglikelihood given class values
		/// and estimated probablities.
		/// </summary>
		private double CalculateLogLikelihood(double[][] trainYs, double[][] probs)
		{
			
			double logLikelihood = 0;
			for (int i = 0; i < trainYs.Length; i++)
			{
				for (int j = 0; j < m_NumClasses; j++)
				{
					if (trainYs[i][j] == 1.0 - m_Offset)
					{
						logLikelihood -= System.Math.Log(probs[i][j]);
					}
				}
			}
			return logLikelihood / (double) trainYs.Length;
		}
		
		/// <summary> Performs one boosting iteration.</summary>
		private void  performIteration(double[][] trainYs, double[][] trainFs, double[][] probs, Instances data, double origSumOfWeights)
		{
			
			if (m_Debug)
			{
				System.Console.Error.WriteLine("Training classifier " + (m_NumGenerated + 1));
			}
			
			// Build the new models
			for (int j = 0; j < m_NumClasses; j++)
			{
				if (m_Debug)
				{
					System.Console.Error.WriteLine("\t...for class " + (j + 1) + " (" + m_ClassAttribute.name() + "=" + m_ClassAttribute.value_Renamed(j) + ")");
				}
				
				// Make copy because we want to save the weights
				Instances boostData = new Instances(data);
				
				// Set instance pseudoclass and weights
				for (int i = 0; i < probs.Length; i++)
				{
					
					// Compute response and weight
					double p = probs[i][j];
					double z, actual = trainYs[i][j];
					if (actual == 1 - m_Offset)
					{
						z = 1.0 / p;
						if (z > Z_MAX)
						{
							// threshold
							z = Z_MAX;
						}
					}
					else
					{
						z = (- 1.0) / (1.0 - p);
						if (z < - Z_MAX)
						{
							// threshold
							z = - Z_MAX;
						}
					}
					double w = (actual - p) / z;
					
					// Set values for instance
					Instance current = boostData.instance(i);
					current.setValue(boostData.classIndex(), z);
					current.Weight = current.weight() * w;
				}
				
				// Scale the weights (helps with some base learners)
				double sumOfWeights = boostData.sumOfWeights();
				double scalingFactor = (double) origSumOfWeights / sumOfWeights;
				for (int i = 0; i < probs.Length; i++)
				{
					Instance current = boostData.instance(i);
					current.Weight = current.weight() * scalingFactor;
				}
				
				// Select instances to train the classifier on
				Instances trainData = boostData;
				if (m_WeightThreshold < 100)
				{
					trainData = selectWeightQuantile(boostData, (double) m_WeightThreshold / 100);
				}
				else
				{
					if (m_UseResampling)
					{
						double[] weights = new double[boostData.numInstances()];
						for (int kk = 0; kk < weights.Length; kk++)
						{
							weights[kk] = boostData.instance(kk).weight();
						}
						trainData = boostData.resampleWithWeights(m_RandomInstance, weights);
					}
				}
				
				// Build the classifier
				m_Classifiers[j][m_NumGenerated].buildClassifier(trainData);
			}
			
			// Evaluate / increment trainFs from the classifier
			for (int i = 0; i < trainFs.Length; i++)
			{
				double[] pred = new double[m_NumClasses];
				double predSum = 0;
				for (int j = 0; j < m_NumClasses; j++)
				{
					pred[j] = m_Shrinkage * m_Classifiers[j][m_NumGenerated].classifyInstance(data.instance(i));
					predSum += pred[j];
				}
				predSum /= m_NumClasses;
				for (int j = 0; j < m_NumClasses; j++)
				{
					trainFs[i][j] += (pred[j] - predSum) * (m_NumClasses - 1) / m_NumClasses;
				}
			}
			m_NumGenerated++;
			
			// Compute the current probability estimates
			for (int i = 0; i < trainYs.Length; i++)
			{
                probs[i] = Calculateprobs(trainFs[i]);
			}
		}
		
		/// <summary> Returns the array of classifiers that have been built.</summary>
		public virtual Classifier[][] classifiers()
		{
			
			Classifier[][] classifiers = new Classifier[m_NumClasses][];
			for (int i = 0; i < m_NumClasses; i++)
			{
				classifiers[i] = new Classifier[m_NumGenerated];
			}
			for (int j = 0; j < m_NumClasses; j++)
			{
				for (int i = 0; i < m_NumGenerated; i++)
				{
					classifiers[j][i] = m_Classifiers[j][i];
				}
			}
			return classifiers;
		}
		
		/// <summary> Computes probabilities from F scores</summary>
		private double[] Calculateprobs(double[] Fs)
		{
			
			//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
			double maxF = - System.Double.MaxValue;
			for (int i = 0; i < Fs.Length; i++)
			{
				if (Fs[i] > maxF)
				{
					maxF = Fs[i];
				}
			}
			double sum = 0;
			double[] probs = new double[Fs.Length];
			for (int i = 0; i < Fs.Length; i++)
			{
				probs[i] = System.Math.Exp(Fs[i] - maxF);
				sum += probs[i];
			}
			Utils.normalize(probs, sum);
			return probs;
		}
		
		/// <summary> Calculates the class membership probabilities for the given test instance.
		/// 
		/// </summary>
		/// <param name="instance">the instance to be classified
		/// </param>
		/// <returns> predicted class probability distribution
		/// </returns>
		/// <exception cref="Exception">if instance could not be classified
		/// successfully
		/// </exception>
		public virtual double[] distributionForInstance(Instance instance)
		{
			
			instance = (Instance) instance.copy();
			instance.Dataset = m_NumericClassData;
			double[] pred = new double[m_NumClasses];
			double[] Fs = new double[m_NumClasses];
			for (int i = 0; i < m_NumGenerated; i++)
			{
				double predSum = 0;
				for (int j = 0; j < m_NumClasses; j++)
				{
					pred[j] = m_Classifiers[j][i].classifyInstance(instance);
					predSum += pred[j];
				}
				predSum /= m_NumClasses;
				for (int j = 0; j < m_NumClasses; j++)
				{
					Fs[j] += (pred[j] - predSum) * (m_NumClasses - 1) / m_NumClasses;
				}
			}

            return Calculateprobs(Fs);
		}
		
		/// <summary> Returns the boosted model as Java source code.
		/// 
		/// </summary>
		/// <returns> the tree as Java source code
		/// </returns>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public virtual System.String toSource(System.String className)
		{
			
			if (m_NumGenerated == 0)
			{
				throw new System.Exception("No model built yet");
			}
			if (!(m_Classifiers[0][0] is Sourcable))
			{
				throw new System.Exception("Base learner " + m_Classifier.ToString() + " is not Sourcable");
			}
			
			System.Text.StringBuilder text = new System.Text.StringBuilder("class ");
			text.Append(className).Append(" {\n\n");
			text.Append("  private static double RtoP(double []R, int j) {\n" + "    double Rcenter = 0;\n" + "    for (int i = 0; i < R.length; i++) {\n" + "      Rcenter += R[i];\n" + "    }\n" + "    Rcenter /= R.length;\n" + "    double Rsum = 0;\n" + "    for (int i = 0; i < R.length; i++) {\n" + "      Rsum += Math.exp(R[i] - Rcenter);\n" + "    }\n" + "    return Math.exp(R[j]) / Rsum;\n" + "  }\n\n");
			
			text.Append("  public static double classify(Object [] i) {\n" + "    double [] d = distribution(i);\n" + "    double maxV = d[0];\n" + "    int maxI = 0;\n" + "    for (int j = 1; j < " + m_NumClasses + "; j++) {\n" + "      if (d[j] > maxV) { maxV = d[j]; maxI = j; }\n" + "    }\n    return (double) maxI;\n  }\n\n");
			
			text.Append("  public static double [] distribution(Object [] i) {\n");
			text.Append("    double [] Fs = new double [" + m_NumClasses + "];\n");
			text.Append("    double [] Fi = new double [" + m_NumClasses + "];\n");
			text.Append("    double Fsum;\n");
			for (int i = 0; i < m_NumGenerated; i++)
			{
				text.Append("    Fsum = 0;\n");
				for (int j = 0; j < m_NumClasses; j++)
				{
					text.Append("    Fi[" + j + "] = " + className + '_' + j + '_' + i + ".classify(i); Fsum += Fi[" + j + "];\n");
				}
				text.Append("    Fsum /= " + m_NumClasses + ";\n");
				text.Append("    for (int j = 0; j < " + m_NumClasses + "; j++) {");
				text.Append(" Fs[j] += (Fi[j] - Fsum) * " + (m_NumClasses - 1) + " / " + m_NumClasses + "; }\n");
			}
			
			text.Append("    double [] dist = new double [" + m_NumClasses + "];\n" + "    for (int j = 0; j < " + m_NumClasses + "; j++) {\n" + "      dist[j] = RtoP(Fs, j);\n" + "    }\n    return dist;\n");
			text.Append("  }\n}\n");
			
			for (int i = 0; i < m_Classifiers.Length; i++)
			{
				for (int j = 0; j < m_Classifiers[i].Length; j++)
				{
					text.Append(((Sourcable) m_Classifiers[i][j]).toSource(className + '_' + i + '_' + j));
				}
			}
			return text.ToString();
		}
		
		/// <summary> Returns description of the boosted classifier.
		/// 
		/// </summary>
		/// <returns> description of the boosted classifier as a string
		/// </returns>
		public override System.String ToString()
		{
			
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			
			if (m_NumGenerated == 0)
			{
				text.Append("LogitBoost: No model built yet.");
				//      text.append(m_Classifiers[0].toString()+"\n");
			}
			else
			{
				text.Append("LogitBoost: Base classifiers and their weights: \n");
				for (int i = 0; i < m_NumGenerated; i++)
				{
					text.Append("\nIteration " + (i + 1));
					for (int j = 0; j < m_NumClasses; j++)
					{
						//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Object.toString' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
						text.Append("\n\tClass " + (j + 1) + " (" + m_ClassAttribute.name() + "=" + m_ClassAttribute.value_Renamed(j) + ")\n\n" + m_Classifiers[j][i].ToString() + "\n");
					}
				}
				text.Append("Number of performed iterations: " + m_NumGenerated + "\n");
			}
			
			return text.ToString();
		}



        override public System.Object Clone()
        {
            return null;
        }
	}
}