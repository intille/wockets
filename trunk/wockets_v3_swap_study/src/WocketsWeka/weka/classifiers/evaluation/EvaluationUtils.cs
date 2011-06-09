/*
*    EvaluationUtils.java
*    Copyright (C) 2002 University of Waikato
*
*/
using System;
using FastVector = weka.core.FastVector;
using Instance = weka.core.Instance;
using Instances = weka.core.Instances;
using Classifier = weka.classifiers.Classifier;
namespace weka.classifiers.evaluation
{
	
	/// <summary> Contains utility functions for generating lists of predictions in 
	/// various manners.
	/// 
	/// </summary>
	/// <author>  Len Trigg (len@reeltwo.com)
	/// </author>
	/// <version>  $Revision: 1.9 $
	/// </version>
	public class EvaluationUtils
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary>Gets the seed for randomization during cross-validation </summary>
		/// <summary>Sets the seed for randomization during cross-validation </summary>
		virtual public int Seed
		{
			get
			{
				return m_Seed;
			}
			
			set
			{
				m_Seed = value;
			}
			
		}
		
		/// <summary>Seed used to randomize data in cross-validation </summary>
		private int m_Seed = 1;
		
		/// <summary> Generate a bunch of predictions ready for processing, by performing a
		/// cross-validation on the supplied dataset.
		/// 
		/// </summary>
		/// <param name="classifier">the Classifier to evaluate
		/// </param>
		/// <param name="data">the dataset
		/// </param>
		/// <param name="numFolds">the number of folds in the cross-validation.
		/// </param>
		/// <exception cref="Exception">if an error occurs
		/// </exception>
		public virtual FastVector getCVPredictions(Classifier classifier, Instances data, int numFolds)
		{
			
			FastVector predictions = new FastVector();
			Instances runInstances = new Instances(data);
			//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.util.Random.Random'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
			System.Random random = new System.Random((System.Int32) m_Seed);
			runInstances.randomize(random);
			if (runInstances.classAttribute().Nominal && (numFolds > 1))
			{
				runInstances.stratify(numFolds);
			}
			//int inst = 0;
			for (int fold = 0; fold < numFolds; fold++)
			{
				Instances train = runInstances.trainCV(numFolds, fold, random);
				Instances test = runInstances.testCV(numFolds, fold);
				FastVector foldPred = getTrainTestPredictions(classifier, train, test);
				predictions.appendXmlElements(foldPred);
			}
			return predictions;
		}
		
		/// <summary> Generate a bunch of predictions ready for processing, by performing a
		/// evaluation on a test set after training on the given training set.
		/// 
		/// </summary>
		/// <param name="classifier">the Classifier to evaluate
		/// </param>
		/// <param name="train">the training dataset
		/// </param>
		/// <param name="test">the test dataset
		/// </param>
		/// <exception cref="Exception">if an error occurs
		/// </exception>
		public virtual FastVector getTrainTestPredictions(Classifier classifier, Instances train, Instances test)
		{
			
			classifier.buildClassifier(train);
			return getTestPredictions(classifier, test);
		}
		
		/// <summary> Generate a bunch of predictions ready for processing, by performing a
		/// evaluation on a test set assuming the classifier is already trained.
		/// 
		/// </summary>
		/// <param name="classifier">the pre-trained Classifier to evaluate
		/// </param>
		/// <param name="test">the test dataset
		/// </param>
		/// <exception cref="Exception">if an error occurs
		/// </exception>
		public virtual FastVector getTestPredictions(Classifier classifier, Instances test)
		{
			
			FastVector predictions = new FastVector();
			for (int i = 0; i < test.numInstances(); i++)
			{
				if (!test.instance(i).classIsMissing())
				{
					predictions.addElement(getPrediction(classifier, test.instance(i)));
				}
			}
			return predictions;
		}
		
		
		/// <summary> Generate a single prediction for a test instance given the pre-trained
		/// classifier.
		/// 
		/// </summary>
		/// <param name="classifier">the pre-trained Classifier to evaluate
		/// </param>
		/// <param name="test">the test instance
		/// </param>
		/// <exception cref="Exception">if an error occurs
		/// </exception>
		public virtual Prediction getPrediction(Classifier classifier, Instance test)
		{
			
			double actual = test.classValue();
			double[] dist = classifier.distributionForInstance(test);
			if (test.classAttribute().Nominal)
			{
				return new NominalPrediction(actual, dist, test.weight());
			}
			else
			{
				return new NumericPrediction(actual, dist[0], test.weight());
			}
		}
	}
}