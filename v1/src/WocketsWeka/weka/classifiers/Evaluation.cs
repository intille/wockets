/*
*    Evaluation.java
*    Copyright (C) 1999 Eibe Frank,Len Trigg
*/
using System;
using weka.core;
//UPGRADE_TODO: The package 'weka.estimators' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using weka.estimators;
using ICSharpCode.SharpZipLib.GZip;
#if !PocketPC
using System.Runtime.Serialization.Formatters.Binary;
#endif

namespace weka.classifiers
{
	
	/// <summary> Class for evaluating machine learning models. <p/>
	/// 
	/// ------------------------------------------------------------------- <p/>
	/// 
	/// General options when evaluating a learning scheme from the command-line: <p/>
	/// 
	/// -t filename <br/>
	/// Name of the file with the training data. (required) <p/>
	/// 
	/// -T filename <br/>
	/// Name of the file with the test data. If missing a cross-validation 
	/// is performed. <p/>
	/// 
	/// -c index <br/>
	/// Index of the class attribute (1, 2, ...; default: last). <p/>
	/// 
	/// -x number <br/>
	/// The number of folds for the cross-validation (default: 10). <p/>
	/// 
	/// -s seed <br/>
	/// Random number seed for the cross-validation (default: 1). <p/>
	/// 
	/// -m filename <br/>
	/// The name of a file containing a cost matrix. <p/>
	/// 
	/// -l filename <br/>
	/// Loads classifier from the given file. <p/>
	/// 
	/// -d filename <br/>
	/// Saves classifier built from the training data into the given file. <p/>
	/// 
	/// -v <br/>
	/// Outputs no statistics for the training data. <p/>
	/// 
	/// -o <br/>
	/// Outputs statistics only, not the classifier. <p/>
	/// 
	/// -i <br/>
	/// Outputs information-retrieval statistics per class. <p/>
	/// 
	/// -k <br/>
	/// Outputs information-theoretic statistics. <p/>
	/// 
	/// -p range <br/>
	/// Outputs predictions for test instances, along with the attributes in 
	/// the specified range (and nothing else). Use '-p 0' if no attributes are
	/// desired. <p/>
	/// 
	/// -r <br/>
	/// Outputs cumulative margin distribution (and nothing else). <p/>
	/// 
	/// -g <br/> 
	/// Only for classifiers that implement "Graphable." Outputs
	/// the graph representation of the classifier (and nothing
	/// else). <p/>
	/// 
	/// ------------------------------------------------------------------- <p/>
	/// 
	/// Example usage as the main of a classifier (called FunkyClassifier):
	/// <code> <pre>
	/// public static void main(String [] args) {
	/// try {
	/// Classifier scheme = new FunkyClassifier();
	/// System.out.println(Evaluation.evaluateModel(scheme, args));
	/// } catch (Exception e) {
	/// System.err.println(e.getMessage());
	/// }
	/// }
	/// </pre> </code> 
	/// <p/>
	/// 
	/// ------------------------------------------------------------------ <p/>
	/// 
	/// Example usage from within an application:
	/// <code> <pre>
	/// Instances trainInstances = ... instances got from somewhere
	/// Instances testInstances = ... instances got from somewhere
	/// Classifier scheme = ... scheme got from somewhere
	/// 
	/// Evaluation evaluation = new Evaluation(trainInstances);
	/// evaluation.evaluateModel(scheme, testInstances);
	/// System.out.println(evaluation.toSummaryString());
	/// </pre> </code> 
	/// 
	/// 
	/// </summary>
	/// <author>    Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <author>    Len Trigg (trigg@cs.waikato.ac.nz)
	/// </author>
	/// <version>   $Revision: 1.53.2.5 $
	/// </version>
	public class Evaluation : Summarizable
	{
		/// <summary> Sets the class prior probabilities
		/// 
		/// </summary>
		/// <param name="train">the training instances used to determine
		/// the prior probabilities
		/// </param>
		/// <throws>  Exception if the class attribute of the instances is not </throws>
		/// <summary> set
		/// </summary>
		virtual public Instances Priors
		{
			set
			{
				m_NoPriors = false;
				
				if (!m_ClassIsNominal)
				{
					
					m_NumTrainClassVals = 0;
					m_TrainClassVals = null;
					m_TrainClassWeights = null;
					m_PriorErrorEstimator = null;
					m_ErrorEstimator = null;
					
					for (int i = 0; i < value.numInstances(); i++)
					{
						Instance currentInst = value.instance(i);
						if (!currentInst.classIsMissing())
						{
							addNumericTrainClass(currentInst.classValue(), currentInst.weight());
						}
					}
				}
				else
				{
					for (int i = 0; i < m_NumClasses; i++)
					{
						m_ClassPriors[i] = 1;
					}
					m_ClassPriorsSum = m_NumClasses;
					for (int i = 0; i < value.numInstances(); i++)
					{
						if (!value.instance(i).classIsMissing())
						{
							//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
							m_ClassPriors[(int) value.instance(i).classValue()] += value.instance(i).weight();
							m_ClassPriorsSum += value.instance(i).weight();
						}
					}
				}
			}
			
		}
		/// <summary>The number of classes. </summary>
		protected internal int m_NumClasses;
		/// <summary>The number of folds for a cross-validation. </summary>
		protected internal int m_NumFolds;
		/// <summary>The weight of all incorrectly classified instances. </summary>
		protected internal double m_Incorrect;
		/// <summary>The weight of all correctly classified instances. </summary>
		protected internal double m_Correct;
		/// <summary>The weight of all unclassified instances. </summary>
		protected internal double m_Unclassified;
		/// <summary> The weight of all instances that had no class assigned to them. </summary>
		protected internal double m_MissingClass;
		/// <summary>The weight of all instances that had a class assigned to them. </summary>
		protected internal double m_WithClass;
		/// <summary>Array for storing the confusion matrix. </summary>
		protected internal double[][] m_ConfusionMatrix;
		/// <summary>The names of the classes. </summary>
		protected internal System.String[] m_ClassNames;
		/// <summary>Is the class nominal or numeric? </summary>
		protected internal bool m_ClassIsNominal;
		/// <summary>The prior probabilities of the classes </summary>
		protected internal double[] m_ClassPriors;
		/// <summary>The sum of counts for priors </summary>
		protected internal double m_ClassPriorsSum;
		/// <summary>The cost matrix (if given). </summary>
		protected internal CostMatrix m_CostMatrix;
		/// <summary>The total cost of predictions (includes instance weights) </summary>
		protected internal double m_TotalCost;
		/// <summary>Sum of errors. </summary>
		protected internal double m_SumErr;
		/// <summary>Sum of absolute errors. </summary>
		protected internal double m_SumAbsErr;
		/// <summary>Sum of squared errors. </summary>
		protected internal double m_SumSqrErr;
		/// <summary>Sum of class values. </summary>
		protected internal double m_SumClass;
		/// <summary>Sum of squared class values. </summary>
		protected internal double m_SumSqrClass;
		/// <summary> Sum of predicted values. </summary>
		protected internal double m_SumPredicted;
		/// <summary>Sum of squared predicted values. </summary>
		protected internal double m_SumSqrPredicted;
		/// <summary>Sum of predicted * class values. </summary>
		protected internal double m_SumClassPredicted;
		/// <summary>Sum of absolute errors of the prior </summary>
		protected internal double m_SumPriorAbsErr;
		/// <summary>Sum of absolute errors of the prior </summary>
		protected internal double m_SumPriorSqrErr;
		/// <summary>Total Kononenko & Bratko Information </summary>
		protected internal double m_SumKBInfo;
		/// <summary> Resolution of the margin histogram </summary>
		protected internal static int k_MarginResolution = 500;
		/// <summary>Cumulative margin distribution </summary>
		protected internal double[] m_MarginCounts;
		/// <summary>Number of non-missing class training instances seen </summary>
		protected internal int m_NumTrainClassVals;
		/// <summary>Array containing all numeric training class values seen </summary>
		protected internal double[] m_TrainClassVals;
		/// <summary>Array containing all numeric training class weights </summary>
		protected internal double[] m_TrainClassWeights;
		/// <summary>Numeric class error estimator for prior </summary>
		protected internal Estimator m_PriorErrorEstimator;
		/// <summary>Numeric class error estimator for scheme </summary>
		protected internal Estimator m_ErrorEstimator;
		/// <summary> The minimum probablility accepted from an estimator to avoid
		/// taking log(0) in Sf calculations.
		/// </summary>
		//UPGRADE_NOTE: Final was removed from the declaration of 'MIN_SF_PROB '. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1003'"
		//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MIN_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
		protected internal static readonly double MIN_SF_PROB = System.Double.MinValue;
		/// <summary>Total entropy of prior predictions </summary>
		protected internal double m_SumPriorEntropy;
		/// <summary>Total entropy of scheme predictions </summary>
		protected internal double m_SumSchemeEntropy;
		/// <summary>enables/disables the use of priors, e.g., if no training set is
		/// present in case of de-serialized schemes 
		/// </summary>
		protected internal bool m_NoPriors = false;
		
		/// <summary> Initializes all the counters for the evaluation.
		/// Use <code>useNoPriors()</code> if the dataset is the test set and you
		/// can't initialize with the priors from the training set via 
		/// <code>setPriors(Instances)</code>.
		/// 
		/// </summary>
		/// <param name="data">	set of training instances, to get some header 
		/// information and prior class distribution information
		/// </param>
		/// <throws>  Exception 	if the class is not defined </throws>
		/// <seealso cref="useNoPriors()">
		/// </seealso>
		/// <seealso cref="setPriors(Instances)">
		/// </seealso>
		public Evaluation(Instances data):this(data, null)
		{
		}
		
		/// <summary> Initializes all the counters for the evaluation and also takes a
		/// cost matrix as parameter.
		/// Use <code>useNoPriors()</code> if the dataset is the test set and you
		/// can't initialize with the priors from the training set via 
		/// <code>setPriors(Instances)</code>.
		/// 
		/// </summary>
		/// <param name="data">	set of training instances, to get some header 
		/// information and prior class distribution information
		/// </param>
		/// <param name="costMatrix">	the cost matrix---if null, default costs will be used
		/// </param>
		/// <throws>  Exception 	if cost matrix is not compatible with  </throws>
		/// <summary> 			data, the class is not defined or the class is numeric
		/// </summary>
		/// <seealso cref="useNoPriors()">
		/// </seealso>
		/// <seealso cref="setPriors(Instances)">
		/// </seealso>
		public Evaluation(Instances data, CostMatrix costMatrix)
		{
			
			m_NumClasses = data.numClasses();
			m_NumFolds = 1;
			m_ClassIsNominal = data.classAttribute().Nominal;
			
			if (m_ClassIsNominal)
			{
				double[][] tmpArray = new double[m_NumClasses][];
				for (int i = 0; i < m_NumClasses; i++)
				{
					tmpArray[i] = new double[m_NumClasses];
				}
				m_ConfusionMatrix = tmpArray;
				m_ClassNames = new System.String[m_NumClasses];
				for (int i = 0; i < m_NumClasses; i++)
				{
					m_ClassNames[i] = data.classAttribute().value_Renamed(i);
				}
			}
			m_CostMatrix = costMatrix;
			if (m_CostMatrix != null)
			{
				if (!m_ClassIsNominal)
				{
					throw new System.Exception("Class has to be nominal if cost matrix " + "given!");
				}
				if (m_CostMatrix.size() != m_NumClasses)
				{
					throw new System.Exception("Cost matrix not compatible with data!");
				}
			}
			m_ClassPriors = new double[m_NumClasses];
			Priors = data;
			m_MarginCounts = new double[k_MarginResolution + 1];
		}
		
		/// <summary> Returns a copy of the confusion matrix.
		/// 
		/// </summary>
		/// <returns> a copy of the confusion matrix as a two-dimensional array
		/// </returns>
		public virtual double[][] confusionMatrix()
		{
			
			double[][] newMatrix = new double[m_ConfusionMatrix.Length][];
			for (int i = 0; i < m_ConfusionMatrix.Length; i++)
			{
				newMatrix[i] = new double[0];
			}
			
			for (int i = 0; i < m_ConfusionMatrix.Length; i++)
			{
				newMatrix[i] = new double[m_ConfusionMatrix[i].Length];
				Array.Copy(m_ConfusionMatrix[i], 0, newMatrix[i], 0, m_ConfusionMatrix[i].Length);
			}
			return newMatrix;
		}
		
		/// <summary> Performs a (stratified if class is nominal) cross-validation 
		/// for a classifier on a set of instances. Now performs
		/// a deep copy of the classifier before each call to 
		/// buildClassifier() (just in case the classifier is not
		/// initialized properly).
		/// 
		/// </summary>
		/// <param name="classifier">the classifier with any options set.
		/// </param>
		/// <param name="data">the data on which the cross-validation is to be 
		/// performed 
		/// </param>
		/// <param name="numFolds">the number of folds for the cross-validation
		/// </param>
		/// <param name="random">random number generator for randomization 
		/// </param>
		/// <throws>  Exception if a classifier could not be generated  </throws>
		/// <summary> successfully or the class is not defined
		/// </summary>
		public virtual void  crossValidateModel(Classifier classifier, Instances data, int numFolds, System.Random random)
		{
			
			// Make a copy of the data we can reorder
			data = new Instances(data);
			data.randomize(random);
			if (data.classAttribute().Nominal)
			{
				data.stratify(numFolds);
			}
			// Do the folds
			for (int i = 0; i < numFolds; i++)
			{
				Instances train = data.trainCV(numFolds, i, random);
				Priors = train;
				Classifier copiedClassifier = Classifier.makeCopy(classifier);
				copiedClassifier.buildClassifier(train);
				Instances test = data.testCV(numFolds, i);
				evaluateModel(copiedClassifier, test);
			}
			m_NumFolds = numFolds;
		}
		
		/// <summary> Performs a (stratified if class is nominal) cross-validation 
		/// for a classifier on a set of instances.
		/// 
		/// </summary>
		/// <param name="classifierString">a string naming the class of the classifier
		/// </param>
		/// <param name="data">the data on which the cross-validation is to be 
		/// performed 
		/// </param>
		/// <param name="numFolds">the number of folds for the cross-validation
		/// </param>
		/// <param name="options">the options to the classifier. Any options
		/// </param>
		/// <param name="random">the random number generator for randomizing the data
		/// accepted by the classifier will be removed from this array.
		/// </param>
		/// <throws>  Exception if a classifier could not be generated  </throws>
		/// <summary> successfully or the class is not defined
		/// </summary>
		public virtual void  crossValidateModel(System.String classifierString, Instances data, int numFolds, System.String[] options, System.Random random)
		{
			
			crossValidateModel(Classifier.forName(classifierString, options), data, numFolds, random);
        }
#if !PocketPC
		
		/// <summary> Evaluates a classifier with the options given in an array of
		/// strings. <p/>
		/// 
		/// Valid options are: <p/>
		/// 
		/// -t filename <br/>
		/// Name of the file with the training data. (required) <p/>
		/// 
		/// -T filename <br/>
		/// Name of the file with the test data. If missing a cross-validation 
		/// is performed. <p/>
		/// 
		/// -c index <br/>
		/// Index of the class attribute (1, 2, ...; default: last). <p/>
		/// 
		/// -x number <br/>
		/// The number of folds for the cross-validation (default: 10). <p/>
		/// 
		/// -s seed <br/>
		/// Random number seed for the cross-validation (default: 1). <p/>
		/// 
		/// -m filename <br/>
		/// The name of a file containing a cost matrix. <p/>
		/// 
		/// -l filename <br/>
		/// Loads classifier from the given file. <p/>
		/// 
		/// -d filename <br/>
		/// Saves classifier built from the training data into the given file. <p/>
		/// 
		/// -v <br/>
		/// Outputs no statistics for the training data. <p/>
		/// 
		/// -o <br/>
		/// Outputs statistics only, not the classifier. <p/>
		/// 
		/// -i <br/>
		/// Outputs detailed information-retrieval statistics per class. <p/>
		/// 
		/// -k <br/>
		/// Outputs information-theoretic statistics. <p/>
		/// 
		/// -p range <br/>
		/// Outputs predictions for test instances, along with the attributes in 
		/// the specified range (and nothing else). Use '-p 0' if no attributes are
		/// desired. <p/>
		/// 
		/// -r <br/>
		/// Outputs cumulative margin distribution (and nothing else). <p/>
		/// 
		/// -g <br/> 
		/// Only for classifiers that implement "Graphable." Outputs
		/// the graph representation of the classifier (and nothing
		/// else). <p/>
		/// 
		/// </summary>
		/// <param name="classifierString">class of machine learning classifier as a string
		/// </param>
		/// <param name="options">the array of string containing the options
		/// </param>
		/// <throws>  Exception if model could not be evaluated successfully </throws>
		/// <returns> a string describing the results 
		/// </returns>
		public static System.String evaluateModel(System.String classifierString, System.String[] options)
		{
			
			Classifier classifier;
			
			// Create classifier
			try
			{
				//UPGRADE_TODO: The differences in the format  of parameters for method 'java.lang.Class.forName'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
				classifier = (Classifier) System.Activator.CreateInstance(System.Type.GetType(classifierString));
			}
			catch (System.Exception e)
			{
				throw new System.Exception("Can't find class with name " + classifierString + '.');
			}
			return evaluateModel(classifier, options);
        }


        /// <summary> Evaluates a classifier with the options given in an array of
		/// strings. <p/>
		/// 
		/// Valid options are: <p/>
		/// 
		/// -t name of training file <br/>
		/// Name of the file with the training data. (required) <p/>
		/// 
		/// -T name of test file <br/>
		/// Name of the file with the test data. If missing a cross-validation 
		/// is performed. <p/>
		/// 
		/// -c class index <br/>
		/// Index of the class attribute (1, 2, ...; default: last). <p/>
		/// 
		/// -x number of folds <br/>
		/// The number of folds for the cross-validation (default: 10). <p/>
		/// 
		/// -s random number seed <br/>
		/// Random number seed for the cross-validation (default: 1). <p/>
		/// 
		/// -m file with cost matrix <br/>
		/// The name of a file containing a cost matrix. <p/>
		/// 
		/// -l name of model input file <br/>
		/// Loads classifier from the given file. <p/>
		/// 
		/// -d name of model output file <br/>
		/// Saves classifier built from the training data into the given file. <p/>
		/// 
		/// -v <br/>
		/// Outputs no statistics for the training data. <p/>
		/// 
		/// -o <br/>
		/// Outputs statistics only, not the classifier. <p/>
		/// 
		/// -i <br/>
		/// Outputs detailed information-retrieval statistics per class. <p/>
		/// 
		/// -k <br/>
		/// Outputs information-theoretic statistics. <p/>
		/// 
		/// -p <br/>
		/// Outputs predictions for test instances (and nothing else). <p/>
		/// 
		/// -r <br/>
		/// Outputs cumulative margin distribution (and nothing else). <p/>
		/// 
		/// -g <br/> 
		/// Only for classifiers that implement "Graphable." Outputs
		/// the graph representation of the classifier (and nothing
		/// else). <p/>
		/// 
		/// </summary>
		/// <param name="classifier">machine learning classifier
		/// </param>
		/// <param name="options">the array of string containing the options
		/// </param>
		/// <throws>  Exception if model could not be evaluated successfully </throws>
		/// <returns> a string describing the results 
		/// </returns>
		public static System.String evaluateModel(Classifier classifier, System.String[] options)
		{
			
			Instances train = null, tempTrain, test = null, template = null;
			int seed = 1, folds = 10, classIndex = - 1;
			System.String trainFileName, testFileName, sourceClass, classIndexString, seedString, foldsString, objectInputFileName, objectOutputFileName, attributeRangeString;
			bool noOutput = false, printClassifications = false, trainStatistics = true, printMargins = false, printComplexityStatistics = false, printGraph = false, classStatistics = false, printSource = false;
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			System.IO.StreamReader trainReader = null, testReader = null;
			//UPGRADE_TODO: Class 'java.io.ObjectInputStream' was converted to 'System.IO.BinaryReader' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioObjectInputStream'"
			System.IO.BinaryReader objectInputStream = null;
            System.IO.Stream objectStream=null;
			CostMatrix costMatrix = null;
			System.Text.StringBuilder schemeOptionsText = null;
			Range attributesToOutput = null;
			long trainTimeStart = 0, trainTimeElapsed = 0, testTimeStart = 0, testTimeElapsed = 0;
			Classifier classifierBackup;
			
			try
			{
				
				// Get basic options (options the same for all schemes)
				classIndexString = Utils.getOption('c', options);
				if (classIndexString.Length != 0)
				{
					if (classIndexString.Equals("first"))
						classIndex = 1;
					else if (classIndexString.Equals("last"))
						classIndex = - 1;
					else
						classIndex = System.Int32.Parse(classIndexString);
				}
				trainFileName = Utils.getOption('t', options);
				objectInputFileName = Utils.getOption('l', options);
				objectOutputFileName = Utils.getOption('d', options);
				testFileName = Utils.getOption('T', options);
				if (trainFileName.Length == 0)
				{
					if (objectInputFileName.Length == 0)
					{
						throw new System.Exception("No training file and no object " + "input file given.");
					}
					if (testFileName.Length == 0)
					{
						throw new System.Exception("No training file and no test " + "file given.");
					}
				}
				else if ((objectInputFileName.Length != 0) && ((!(classifier is UpdateableClassifier)) || (testFileName.Length == 0)))
				{
					throw new System.Exception("Classifier not incremental, or no " + "test file provided: can't " + "use both train and model file.");
				}
				try
				{
					if (trainFileName.Length != 0)
					{
						//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.io.BufferedReader.BufferedReader'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
						//UPGRADE_WARNING: At least one expression was used more than once in the target code. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1181'"
						//UPGRADE_TODO: Constructor 'java.io.FileReader.FileReader' was converted to 'System.IO.StreamReader' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073'"
						trainReader = new System.IO.StreamReader(new System.IO.StreamReader(trainFileName, System.Text.Encoding.Default).BaseStream, new System.IO.StreamReader(trainFileName, System.Text.Encoding.Default).CurrentEncoding);
					}
					if (testFileName.Length != 0)
					{
						//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.io.BufferedReader.BufferedReader'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
						//UPGRADE_WARNING: At least one expression was used more than once in the target code. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1181'"
						//UPGRADE_TODO: Constructor 'java.io.FileReader.FileReader' was converted to 'System.IO.StreamReader' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073'"
						testReader = new System.IO.StreamReader(new System.IO.StreamReader(testFileName, System.Text.Encoding.Default).BaseStream, new System.IO.StreamReader(testFileName, System.Text.Encoding.Default).CurrentEncoding);
					}
					if (objectInputFileName.Length != 0)
					{
						//UPGRADE_TODO: Constructor 'java.io.FileInputStream.FileInputStream' was converted to 'System.IO.FileStream.FileStream' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioFileInputStreamFileInputStream_javalangString'"
						objectStream= new System.IO.FileStream(objectInputFileName, System.IO.FileMode.Open, System.IO.FileAccess.Read);
						if (objectInputFileName.EndsWith(".gz"))
						{
							//UPGRADE_ISSUE: Constructor 'java.util.zip.GZIPInputStream.GZIPInputStream' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javautilzipGZIPInputStream'"
							objectStream= new ICSharpCode.SharpZipLib.GZip.GZipInputStream(objectStream);
						}
						//UPGRADE_TODO: Class 'java.io.ObjectInputStream' was converted to 'System.IO.BinaryReader' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioObjectInputStream'"
						objectInputStream = new System.IO.BinaryReader(objectStream);
					}
				}
				catch (System.Exception e)
				{
					//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Throwable.getMessage' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
					throw new System.Exception("Can't open file " + e.Message + '.');
				}
				if (testFileName.Length != 0)
				{
					template = test = new Instances(testReader, 1);
					if (classIndex != - 1)
					{
						test.ClassIndex = classIndex - 1;
					}
					else
					{
						test.ClassIndex = test.numAttributes() - 1;
					}
					if (classIndex > test.numAttributes())
					{
						throw new System.Exception("Index of class attribute too large.");
					}
				}
				if (trainFileName.Length != 0)
				{
					if ((classifier is UpdateableClassifier) && (testFileName.Length != 0))
					{
						train = new Instances(trainReader, 1);
					}
					else
					{
						train = new Instances(trainReader);
					}
					template = train;
					if (classIndex != - 1)
					{
						train.ClassIndex = classIndex - 1;
					}
					else
					{
						train.ClassIndex = train.numAttributes() - 1;
					}
					if ((testFileName.Length != 0) && !test.equalHeaders(train))
					{
						throw new System.ArgumentException("Train and test file not compatible!");
					}
					if (classIndex > train.numAttributes())
					{
						throw new System.Exception("Index of class attribute too large.");
					}
				}
				if (template == null)
				{
					throw new System.Exception("No actual dataset provided to use as template");
				}
				seedString = Utils.getOption('s', options);
				if (seedString.Length != 0)
				{
					seed = System.Int32.Parse(seedString);
				}
				foldsString = Utils.getOption('x', options);
				if (foldsString.Length != 0)
				{
					folds = System.Int32.Parse(foldsString);
				}
				costMatrix = handleCostOption(Utils.getOption('m', options), template.numClasses());
				
				classStatistics = Utils.getFlag('i', options);
				noOutput = Utils.getFlag('o', options);
				trainStatistics = !Utils.getFlag('v', options);
				printComplexityStatistics = Utils.getFlag('k', options);
				printMargins = Utils.getFlag('r', options);
				printGraph = Utils.getFlag('g', options);
				sourceClass = Utils.getOption('z', options);
				printSource = (sourceClass.Length != 0);
				
				// Check -p option
				try
				{
					attributeRangeString = Utils.getOption('p', options);
				}
				catch (System.Exception e)
				{
					//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Throwable.getMessage' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
					throw new System.Exception(e.Message + "\nNOTE: the -p option has changed. " + "It now expects a parameter specifying a range of attributes " + "to list with the predictions. Use '-p 0' for none.");
				}
				if (attributeRangeString.Length != 0)
				{
					// if no test file given, we cannot print predictions
					if (testFileName.Length == 0)
						throw new System.Exception("Cannot print predictions ('-p') without test file ('-T')!");
					
					printClassifications = true;
					if (!attributeRangeString.Equals("0"))
						attributesToOutput = new Range(attributeRangeString);
				}
				
				// if no training file given, we don't have any priors
				if ((trainFileName.Length == 0) && (printComplexityStatistics))
					throw new System.Exception("Cannot print complexity statistics ('-k') without training file ('-t')!");
				
				// If a model file is given, we can't process 
				// scheme-specific options
				if (objectInputFileName.Length != 0)
				{
					Utils.checkForRemainingOptions(options);
				}
				else
				{
					
					// Set options for classifier
					//				if (classifier instanceof OptionHandler) 
					//				{
					//					for (int i = 0; i < options.length; i++) 
					//					{
					//						if (options[i].length() != 0) 
					//						{
					//							if (schemeOptionsText == null) 
					//							{
					//								schemeOptionsText = new StringBuffer();
					//							}
					//							if (options[i].indexOf(' ') != -1) 
					//							{
					//								schemeOptionsText.append('"' + options[i] + "\" ");
					//							} 
					//							else 
					//							{
					//								schemeOptionsText.append(options[i] + " ");
					//							}
					//						}
					//					}
					//					((OptionHandler)classifier).setOptions(options);
					//				}
				}
				Utils.checkForRemainingOptions(options);
			}
			catch (System.Exception e)
			{
				//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Throwable.getMessage' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
				throw new System.Exception("\nWeka exception: " + e.Message + makeOptionString(classifier));
			}
			
			
			// Setup up evaluation objects
			Evaluation trainingEvaluation = new Evaluation(new Instances(template, 0), costMatrix);
			Evaluation testingEvaluation = new Evaluation(new Instances(template, 0), costMatrix);
			
			if (objectInputFileName.Length != 0)
			{
				testingEvaluation.useNoPriors();
				
				// Load classifier from file
				//UPGRADE_WARNING: Method 'java.io.ObjectInputStream.readObject' was converted to 'SupportClass.Deserialize' which may throw an exception. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1101'"
				//classifier = (Classifier) SupportClass.Deserialize(objectInputStream);


                //FileStream fs = new FileStream("DataFile.dat", FileMode.Open);
                try
                {
                    BinaryFormatter formatter = new BinaryFormatter();

                    // Deserialize the hashtable from the file and 
                    // assign the reference to the local variable.
                   // addresses = (Hashtable)formatter.Deserialize(fs);
                    classifier = (Classifier)formatter.Deserialize(objectStream);
                }
                catch (Exception e)
                {
                    Console.WriteLine("Failed to deserialize. Reason: " + e.Message);
                    throw;
                }
                finally
                {
                    objectStream.Close();
                    //fs.Close();
                }


				objectInputStream.Close();
			}
			
			// backup of fully setup classifier for cross-validation
			classifierBackup = Classifier.makeCopy(classifier);
			
			// Build the classifier if no object file provided
			if ((classifier is UpdateableClassifier) && (testFileName.Length != 0) && (costMatrix == null) && (trainFileName.Length != 0))
			{
				
				// Build classifier incrementally
				trainingEvaluation.Priors = train;
				testingEvaluation.Priors = train;
				trainTimeStart = (System.DateTime.Now.Ticks - 621355968000000000) / 10000;
				if (objectInputFileName.Length == 0)
				{
					classifier.buildClassifier(train);
				}
				while (train.readInstance(trainReader))
				{
					
					trainingEvaluation.updatePriors(train.instance(0));
					testingEvaluation.updatePriors(train.instance(0));
					((UpdateableClassifier) classifier).updateClassifier(train.instance(0));
					train.delete(0);
				}
				trainTimeElapsed = (System.DateTime.Now.Ticks - 621355968000000000) / 10000 - trainTimeStart;
				trainReader.Close();
			}
			else if (objectInputFileName.Length == 0)
			{
				
				// Build classifier in one go
				tempTrain = new Instances(train);
				trainingEvaluation.Priors = tempTrain;
				testingEvaluation.Priors = tempTrain;
				trainTimeStart = (System.DateTime.Now.Ticks - 621355968000000000) / 10000;
				classifier.buildClassifier(tempTrain);
				trainTimeElapsed = (System.DateTime.Now.Ticks - 621355968000000000) / 10000 - trainTimeStart;
			}
			
			// Save the classifier if an object output file is provided
			if (objectOutputFileName.Length != 0)
			{
				//UPGRADE_TODO: Constructor 'java.io.FileOutputStream.FileOutputStream' was converted to 'System.IO.FileStream.FileStream' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioFileOutputStreamFileOutputStream_javalangString'"
				System.IO.Stream os = new System.IO.FileStream(objectOutputFileName, System.IO.FileMode.Create);
				if (objectOutputFileName.EndsWith(".gz"))
				{
					//UPGRADE_ISSUE: Constructor 'java.util.zip.GZIPOutputStream.GZIPOutputStream' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javautilzipGZIPOutputStream'"
					os = new ICSharpCode.SharpZipLib.GZip.GZipOutputStream(os);
				}
				//UPGRADE_TODO: Class 'java.io.ObjectOutputStream' was converted to 'System.IO.BinaryWriter' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioObjectOutputStream'"
				System.IO.BinaryWriter objectOutputStream = new System.IO.BinaryWriter(os);
				//UPGRADE_TODO: Method 'java.io.ObjectOutputStream.writeObject' was converted to 'SupportClass.Serialize' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioObjectOutputStreamwriteObject_javalangObject'"
				//SupportClass.Serialize(objectOutputStream, classifier);

                BinaryFormatter bformatter = new BinaryFormatter();
                bformatter.Serialize(os, classifier);                               

				objectOutputStream.Flush();
				objectOutputStream.Close();
			}
			
			// If classifier is drawable output string describing graph
			if ((classifier is Drawable) && (printGraph))
			{
				return ((Drawable) classifier).graph();
			}
			
			// Output the classifier as equivalent source
			if ((classifier is Sourcable) && (printSource))
			{
				return wekaStaticWrapper((Sourcable) classifier, sourceClass);
			}
			
			// Output test instance predictions only
			if (printClassifications)
			{
				return toPrintClassifications(classifier, new Instances(template, 0), testFileName, classIndex, attributesToOutput);
			}
			
			// Output model
			if (!(noOutput || printMargins))
			{
				//			if (classifier instanceof OptionHandler) 
				//			{
				//				if (schemeOptionsText != null) 
				//				{
				//					text.append("\nOptions: "+schemeOptionsText);
				//					text.append("\n");
				//				}
				//			}
				//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Object.toString' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
				text.Append("\n" + classifier.ToString() + "\n");
			}
			
			if (!printMargins && (costMatrix != null))
			{
				text.Append("\n=== Evaluation Cost Matrix ===\n\n").Append(costMatrix.ToString());
			}
			
			// Compute error estimate from training data
			if ((trainStatistics) && (trainFileName.Length != 0))
			{
				
				if ((classifier is UpdateableClassifier) && (testFileName.Length != 0) && (costMatrix == null))
				{
					
					// Classifier was trained incrementally, so we have to 
					// reopen the training data in order to test on it.
					//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.io.BufferedReader.BufferedReader'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
					//UPGRADE_WARNING: At least one expression was used more than once in the target code. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1181'"
					//UPGRADE_TODO: Constructor 'java.io.FileReader.FileReader' was converted to 'System.IO.StreamReader' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073'"
					trainReader = new System.IO.StreamReader(new System.IO.StreamReader(trainFileName, System.Text.Encoding.Default).BaseStream, new System.IO.StreamReader(trainFileName, System.Text.Encoding.Default).CurrentEncoding);
					
					// Incremental testing
					train = new Instances(trainReader, 1);
					if (classIndex != - 1)
					{
						train.ClassIndex = classIndex - 1;
					}
					else
					{
						train.ClassIndex = train.numAttributes() - 1;
					}
					testTimeStart = (System.DateTime.Now.Ticks - 621355968000000000) / 10000;
					while (train.readInstance(trainReader))
					{
						
						trainingEvaluation.evaluateModelOnce((Classifier) classifier, train.instance(0));
						train.delete(0);
					}
					testTimeElapsed = (System.DateTime.Now.Ticks - 621355968000000000) / 10000 - testTimeStart;
					trainReader.Close();
				}
				else
				{
					testTimeStart = (System.DateTime.Now.Ticks - 621355968000000000) / 10000;
					trainingEvaluation.evaluateModel(classifier, train);
					testTimeElapsed = (System.DateTime.Now.Ticks - 621355968000000000) / 10000 - testTimeStart;
				}
				
				// Print the results of the training evaluation
				if (printMargins)
				{
					return trainingEvaluation.toCumulativeMarginDistributionString();
				}
				else
				{
					text.Append("\nTime taken to build model: " + Utils.doubleToString(trainTimeElapsed / 1000.0, 2) + " seconds");
					text.Append("\nTime taken to test model on training data: " + Utils.doubleToString(testTimeElapsed / 1000.0, 2) + " seconds");
					text.Append(trainingEvaluation.toSummaryString("\n\n=== Error on training" + " data ===\n", printComplexityStatistics));
					if (template.classAttribute().Nominal)
					{
						if (classStatistics)
						{
							text.Append("\n\n" + trainingEvaluation.toClassDetailsString());
						}
						text.Append("\n\n" + trainingEvaluation.toMatrixString());
					}
				}
			}
			
			// Compute proper error estimates
			if (testFileName.Length != 0)
			{
				
				// Testing is on the supplied test data
				while (test.readInstance(testReader))
				{
					
					testingEvaluation.evaluateModelOnce((Classifier) classifier, test.instance(0));
					test.delete(0);
				}
				testReader.Close();
				
				text.Append("\n\n" + testingEvaluation.toSummaryString("=== Error on test data ===\n", printComplexityStatistics));
			}
			else if (trainFileName.Length != 0)
			{
				
				// Testing is via cross-validation on training data
				//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.util.Random.Random'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
				System.Random random = new System.Random((System.Int32) seed);
				// use untrained (!) classifier for cross-validation
				classifier = Classifier.makeCopy(classifierBackup);
				testingEvaluation.crossValidateModel(classifier, train, folds, random);
				if (template.classAttribute().Numeric)
				{
					text.Append("\n\n\n" + testingEvaluation.toSummaryString("=== Cross-validation ===\n", printComplexityStatistics));
				}
				else
				{
					text.Append("\n\n\n" + testingEvaluation.toSummaryString("=== Stratified " + "cross-validation ===\n", printComplexityStatistics));
				}
			}
			if (template.classAttribute().Nominal)
			{
				if (classStatistics)
				{
					text.Append("\n\n" + testingEvaluation.toClassDetailsString());
				}
				text.Append("\n\n" + testingEvaluation.toMatrixString());
			}
			return text.ToString();
		}
		
#endif
        /// <summary> Attempts to load a cost matrix.
		/// 
		/// </summary>
		/// <param name="costFileName">the filename of the cost matrix
		/// </param>
		/// <param name="numClasses">the number of classes that should be in the cost matrix
		/// (only used if the cost file is in old format).
		/// </param>
		/// <returns> a <code>CostMatrix</code> value, or null if costFileName is empty
		/// </returns>
		/// <throws>  Exception if an error occurs. </throws>
		protected internal static CostMatrix handleCostOption(System.String costFileName, int numClasses)
		{
			
			if ((costFileName != null) && (costFileName.Length != 0))
			{
				System.Console.Out.WriteLine("NOTE: The behaviour of the -m option has changed between WEKA 3.0" + " and WEKA 3.1. -m now carries out cost-sensitive *evaluation*" + " only. For cost-sensitive *prediction*, use one of the" + " cost-sensitive metaschemes such as" + " weka.classifiers.meta.CostSensitiveClassifier or" + " weka.classifiers.meta.MetaCost");
				
				//UPGRADE_ISSUE: Class hierarchy differences between 'java.io.Reader' and 'System.IO.StreamReader' may cause compilation errors. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1186'"
				System.IO.StreamReader costReader = null;
				try
				{
					//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.io.BufferedReader.BufferedReader'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
					//UPGRADE_WARNING: At least one expression was used more than once in the target code. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1181'"
					//UPGRADE_TODO: Constructor 'java.io.FileReader.FileReader' was converted to 'System.IO.StreamReader' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073'"
					costReader = new System.IO.StreamReader(new System.IO.StreamReader(costFileName, System.Text.Encoding.Default).BaseStream, new System.IO.StreamReader(costFileName, System.Text.Encoding.Default).CurrentEncoding);
				}
				catch (System.Exception e)
				{
					//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Throwable.getMessage' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
					throw new System.Exception("Can't open file " + e.Message + '.');
				}
				try
				{
					// First try as a proper cost matrix format
					return new CostMatrix(costReader);
				}
				catch (System.Exception ex)
				{
					try
					{
						// Now try as the poxy old format :-)
						//System.err.println("Attempting to read old format cost file");
						try
						{
							costReader.Close(); // Close the old one
							//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.io.BufferedReader.BufferedReader'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
							//UPGRADE_WARNING: At least one expression was used more than once in the target code. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1181'"
							//UPGRADE_TODO: Constructor 'java.io.FileReader.FileReader' was converted to 'System.IO.StreamReader' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073'"
							costReader = new System.IO.StreamReader(new System.IO.StreamReader(costFileName, System.Text.Encoding.Default).BaseStream, new System.IO.StreamReader(costFileName, System.Text.Encoding.Default).CurrentEncoding);
						}
						catch (System.Exception e)
						{
							//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Throwable.getMessage' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
							throw new System.Exception("Can't open file " + e.Message + '.');
						}
						CostMatrix costMatrix = new CostMatrix(numClasses);
						//System.err.println("Created default cost matrix");
						costMatrix.readOldFormat(costReader);
						return costMatrix;
						//System.err.println("Read old format");
					}
					catch (System.Exception e2)
					{
						// re-throw the original exception
						//System.err.println("Re-throwing original exception");
						throw ex;
					}
				}
			}
			else
			{
				return null;
			}
		}
		
		/// <summary> Evaluates the classifier on a given set of instances. Note that
		/// the data must have exactly the same format (e.g. order of
		/// attributes) as the data used to train the classifier! Otherwise
		/// the results will generally be meaningless.
		/// 
		/// </summary>
		/// <param name="classifier">machine learning classifier
		/// </param>
		/// <param name="data">set of test instances for evaluation
		/// </param>
		/// <returns> the predictions
		/// </returns>
		/// <throws>  Exception if model could not be evaluated  </throws>
		/// <summary> successfully 
		/// </summary>
		public virtual double[] evaluateModel(Classifier classifier, Instances data)
		{
			
			double[] predictions = new double[data.numInstances()];
			
			for (int i = 0; i < data.numInstances(); i++)
			{
				predictions[i] = evaluateModelOnce((Classifier) classifier, data.instance(i));
			}
			return predictions;
		}
		
		/// <summary> Evaluates the classifier on a single instance.
		/// 
		/// </summary>
		/// <param name="classifier">machine learning classifier
		/// </param>
		/// <param name="instance">the test instance to be classified
		/// </param>
		/// <returns> the prediction made by the clasifier
		/// </returns>
		/// <throws>  Exception if model could not be evaluated  </throws>
		/// <summary> successfully or the data contains string attributes
		/// </summary>
		public virtual double evaluateModelOnce(Classifier classifier, Instance instance)
		{
			
			Instance classMissing = (Instance) instance.copy();
			double pred = 0;
			classMissing.Dataset = instance.dataset();
			classMissing.setClassMissing();
			if (m_ClassIsNominal)
			{
				double[] dist = classifier.distributionForInstance(classMissing);
				pred = Utils.maxIndex(dist);
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				if (dist[(int) pred] <= 0)
				{
					pred = Instance.missingValue();
				}
				updateStatsForClassifier(dist, instance);
			}
			else
			{
				pred = classifier.classifyInstance(classMissing);
				updateStatsForPredictor(pred, instance);
			}
			return pred;
		}
		
		/// <summary> Evaluates the supplied distribution on a single instance.
		/// 
		/// </summary>
		/// <param name="dist">the supplied distribution
		/// </param>
		/// <param name="instance">the test instance to be classified
		/// </param>
		/// <returns> the prediction
		/// </returns>
		/// <throws>  Exception if model could not be evaluated  </throws>
		/// <summary> successfully
		/// </summary>
		public virtual double evaluateModelOnce(double[] dist, Instance instance)
		{
			double pred;
			if (m_ClassIsNominal)
			{
				pred = Utils.maxIndex(dist);
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				if (dist[(int) pred] <= 0)
				{
					pred = Instance.missingValue();
				}
				updateStatsForClassifier(dist, instance);
			}
			else
			{
				pred = dist[0];
				updateStatsForPredictor(pred, instance);
			}
			return pred;
		}
		
		/// <summary> Evaluates the supplied prediction on a single instance.
		/// 
		/// </summary>
		/// <param name="prediction">the supplied prediction
		/// </param>
		/// <param name="instance">the test instance to be classified
		/// </param>
		/// <throws>  Exception if model could not be evaluated  </throws>
		/// <summary> successfully
		/// </summary>
		public virtual void  evaluateModelOnce(double prediction, Instance instance)
		{
			
			if (m_ClassIsNominal)
			{
				updateStatsForClassifier(makeDistribution(prediction), instance);
			}
			else
			{
				updateStatsForPredictor(prediction, instance);
			}
		}
		
		
		/// <summary> Wraps a static classifier in enough source to test using the weka
		/// class libraries.
		/// 
		/// </summary>
		/// <param name="classifier">a Sourcable Classifier
		/// </param>
		/// <param name="className">the name to give to the source code class
		/// </param>
		/// <returns> the source for a static classifier that can be tested with
		/// weka libraries.
		/// </returns>
		/// <throws>  Exception if code-generation fails </throws>
		protected internal static System.String wekaStaticWrapper(Sourcable classifier, System.String className)
		{
			
			//String className = "StaticClassifier";
			System.String staticClassifier = classifier.toSource(className);
			return "package weka.classifiers;\n\n" + "import weka.core.Attribute;\n" + "import weka.core.Instance;\n" + "import weka.core.Instances;\n" + "import weka.classifiers.Classifier;\n\n" + "public class WekaWrapper extends Classifier {\n\n" + "  public void buildClassifier(Instances i) throws Exception {\n" + "  }\n\n" + "  public double classifyInstance(Instance i) throws Exception {\n\n" + "    Object [] s = new Object [i.numAttributes()];\n" + "    for (int j = 0; j < s.length; j++) {\n" + "      if (!i.isMissing(j)) {\n" + "        if (i.attribute(j).type() == Attribute.NOMINAL) {\n" + "          s[j] = i.attribute(j).value((int) i.value(j));\n" + "        } else if (i.attribute(j).type() == Attribute.NUMERIC) {\n" + "          s[j] = new Double(i.value(j));\n" + "        }\n" + "      }\n" + "    }\n" + "    return " + className + ".classify(s);\n" + "  }\n\n" + "}\n\n" + staticClassifier; // The static classifer class
		}
		
		/// <summary> Gets the number of test instances that had a known class value
		/// (actually the sum of the weights of test instances with known 
		/// class value).
		/// 
		/// </summary>
		/// <returns> the number of test instances with known class
		/// </returns>
		public double numInstances()
		{
			
			return m_WithClass;
		}
		
		/// <summary> Gets the number of instances incorrectly classified (that is, for
		/// which an incorrect prediction was made). (Actually the sum of the weights
		/// of these instances)
		/// 
		/// </summary>
		/// <returns> the number of incorrectly classified instances 
		/// </returns>
		public double incorrect()
		{
			
			return m_Incorrect;
		}
		
		/// <summary> Gets the percentage of instances incorrectly classified (that is, for
		/// which an incorrect prediction was made).
		/// 
		/// </summary>
		/// <returns> the percent of incorrectly classified instances 
		/// (between 0 and 100)
		/// </returns>
		public double pctIncorrect()
		{
			
			return 100 * m_Incorrect / m_WithClass;
		}
		
		/// <summary> Gets the total cost, that is, the cost of each prediction times the
		/// weight of the instance, summed over all instances.
		/// 
		/// </summary>
		/// <returns> the total cost
		/// </returns>
		public double totalCost()
		{
			
			return m_TotalCost;
		}
		
		/// <summary> Gets the average cost, that is, total cost of misclassifications
		/// (incorrect plus unclassified) over the total number of instances.
		/// 
		/// </summary>
		/// <returns> the average cost.  
		/// </returns>
		public double avgCost()
		{
			
			return m_TotalCost / m_WithClass;
		}
		
		/// <summary> Gets the number of instances correctly classified (that is, for
		/// which a correct prediction was made). (Actually the sum of the weights
		/// of these instances)
		/// 
		/// </summary>
		/// <returns> the number of correctly classified instances
		/// </returns>
		public double correct()
		{
			
			return m_Correct;
		}
		
		/// <summary> Gets the percentage of instances correctly classified (that is, for
		/// which a correct prediction was made).
		/// 
		/// </summary>
		/// <returns> the percent of correctly classified instances (between 0 and 100)
		/// </returns>
		public double pctCorrect()
		{
			
			return 100 * m_Correct / m_WithClass;
		}
		
		/// <summary> Gets the number of instances not classified (that is, for
		/// which no prediction was made by the classifier). (Actually the sum
		/// of the weights of these instances)
		/// 
		/// </summary>
		/// <returns> the number of unclassified instances
		/// </returns>
		public double unclassified()
		{
			
			return m_Unclassified;
		}
		
		/// <summary> Gets the percentage of instances not classified (that is, for
		/// which no prediction was made by the classifier).
		/// 
		/// </summary>
		/// <returns> the percent of unclassified instances (between 0 and 100)
		/// </returns>
		public double pctUnclassified()
		{
			
			return 100 * m_Unclassified / m_WithClass;
		}
		
		/// <summary> Returns the estimated error rate or the root mean squared error
		/// (if the class is numeric). If a cost matrix was given this
		/// error rate gives the average cost.
		/// 
		/// </summary>
		/// <returns> the estimated error rate (between 0 and 1, or between 0 and 
		/// maximum cost)
		/// </returns>
		public double errorRate()
		{
			
			if (!m_ClassIsNominal)
			{
				return System.Math.Sqrt(m_SumSqrErr / m_WithClass);
			}
			if (m_CostMatrix == null)
			{
				return m_Incorrect / m_WithClass;
			}
			else
			{
				return avgCost();
			}
		}
		
		/// <summary> Returns value of kappa statistic if class is nominal.
		/// 
		/// </summary>
		/// <returns> the value of the kappa statistic
		/// </returns>
		public double kappa()
		{
			
			
			double[] sumRows = new double[m_ConfusionMatrix.Length];
			double[] sumColumns = new double[m_ConfusionMatrix.Length];
			double sumOfWeights = 0;
			for (int i = 0; i < m_ConfusionMatrix.Length; i++)
			{
				for (int j = 0; j < m_ConfusionMatrix.Length; j++)
				{
					sumRows[i] += m_ConfusionMatrix[i][j];
					sumColumns[j] += m_ConfusionMatrix[i][j];
					sumOfWeights += m_ConfusionMatrix[i][j];
				}
			}
			double correct = 0, chanceAgreement = 0;
			for (int i = 0; i < m_ConfusionMatrix.Length; i++)
			{
				chanceAgreement += (sumRows[i] * sumColumns[i]);
				correct += m_ConfusionMatrix[i][i];
			}
			chanceAgreement /= (sumOfWeights * sumOfWeights);
			correct /= sumOfWeights;
			
			if (chanceAgreement < 1)
			{
				return (correct - chanceAgreement) / (1 - chanceAgreement);
			}
			else
			{
				return 1;
			}
		}
		
		/// <summary> Returns the correlation coefficient if the class is numeric.
		/// 
		/// </summary>
		/// <returns> the correlation coefficient
		/// </returns>
		/// <throws>  Exception if class is not numeric </throws>
		public double correlationCoefficient()
		{
			
			if (m_ClassIsNominal)
			{
				throw new System.Exception("Can't compute correlation coefficient: " + "class is nominal!");
			}
			
			double correlation = 0;
			double varActual = m_SumSqrClass - m_SumClass * m_SumClass / m_WithClass;
			double varPredicted = m_SumSqrPredicted - m_SumPredicted * m_SumPredicted / m_WithClass;
			double varProd = m_SumClassPredicted - m_SumClass * m_SumPredicted / m_WithClass;
			
			if (varActual * varPredicted <= 0)
			{
				correlation = 0.0;
			}
			else
			{
				correlation = varProd / System.Math.Sqrt(varActual * varPredicted);
			}
			
			return correlation;
		}
		
		/// <summary> Returns the mean absolute error. Refers to the error of the
		/// predicted values for numeric classes, and the error of the 
		/// predicted probability distribution for nominal classes.
		/// 
		/// </summary>
		/// <returns> the mean absolute error 
		/// </returns>
		public double meanAbsoluteError()
		{
			
			return m_SumAbsErr / m_WithClass;
		}
		
		/// <summary> Returns the mean absolute error of the prior.
		/// 
		/// </summary>
		/// <returns> the mean absolute error 
		/// </returns>
		public double meanPriorAbsoluteError()
		{
			
			if (m_NoPriors)
				return System.Double.NaN;
			
			return m_SumPriorAbsErr / m_WithClass;
		}
		
		/// <summary> Returns the relative absolute error.
		/// 
		/// </summary>
		/// <returns> the relative absolute error 
		/// </returns>
		/// <throws>  Exception if it can't be computed </throws>
		public double relativeAbsoluteError()
		{
			
			if (m_NoPriors)
				return System.Double.NaN;
			
			return 100 * meanAbsoluteError() / meanPriorAbsoluteError();
		}
		
		/// <summary> Returns the root mean squared error.
		/// 
		/// </summary>
		/// <returns> the root mean squared error 
		/// </returns>
		public double rootMeanSquaredError()
		{
			
			return System.Math.Sqrt(m_SumSqrErr / m_WithClass);
		}
		
		/// <summary> Returns the root mean prior squared error.
		/// 
		/// </summary>
		/// <returns> the root mean prior squared error 
		/// </returns>
		public double rootMeanPriorSquaredError()
		{
			
			if (m_NoPriors)
				return System.Double.NaN;
			
			return System.Math.Sqrt(m_SumPriorSqrErr / m_WithClass);
		}
		
		/// <summary> Returns the root relative squared error if the class is numeric.
		/// 
		/// </summary>
		/// <returns> the root relative squared error 
		/// </returns>
		public double rootRelativeSquaredError()
		{
			
			if (m_NoPriors)
				return System.Double.NaN;
			
			return 100.0 * rootMeanSquaredError() / rootMeanPriorSquaredError();
		}
		
		/// <summary> Calculate the entropy of the prior distribution
		/// 
		/// </summary>
		/// <returns> the entropy of the prior distribution
		/// </returns>
		/// <throws>  Exception if the class is not nominal </throws>
		public double priorEntropy()
		{
			
			if (!m_ClassIsNominal)
			{
				throw new System.Exception("Can't compute entropy of class prior: " + "class numeric!");
			}
			
			if (m_NoPriors)
				return System.Double.NaN;
			
			double entropy = 0;
			for (int i = 0; i < m_NumClasses; i++)
			{
				entropy -= m_ClassPriors[i] / m_ClassPriorsSum * Utils.log2(m_ClassPriors[i] / m_ClassPriorsSum);
			}
			return entropy;
		}
		
		
		/// <summary> Return the total Kononenko & Bratko Information score in bits
		/// 
		/// </summary>
		/// <returns> the K&B information score
		/// </returns>
		/// <throws>  Exception if the class is not nominal </throws>
		public double KBInformation()
		{
			
			if (!m_ClassIsNominal)
			{
				throw new System.Exception("Can't compute K&B Info score: " + "class numeric!");
			}
			
			if (m_NoPriors)
				return System.Double.NaN;
			
			return m_SumKBInfo;
		}
		
		/// <summary> Return the Kononenko & Bratko Information score in bits per 
		/// instance.
		/// 
		/// </summary>
		/// <returns> the K&B information score
		/// </returns>
		/// <throws>  Exception if the class is not nominal </throws>
		public double KBMeanInformation()
		{
			
			if (!m_ClassIsNominal)
			{
				throw new System.Exception("Can't compute K&B Info score: " + "class numeric!");
			}
			
			if (m_NoPriors)
				return System.Double.NaN;
			
			return m_SumKBInfo / m_WithClass;
		}
		
		/// <summary> Return the Kononenko & Bratko Relative Information score
		/// 
		/// </summary>
		/// <returns> the K&B relative information score
		/// </returns>
		/// <throws>  Exception if the class is not nominal </throws>
		public double KBRelativeInformation()
		{
			
			if (!m_ClassIsNominal)
			{
				throw new System.Exception("Can't compute K&B Info score: " + "class numeric!");
			}
			
			if (m_NoPriors)
				return System.Double.NaN;
			
			return 100.0 * KBInformation() / priorEntropy();
		}
		
		/// <summary> Returns the total entropy for the null model
		/// 
		/// </summary>
		/// <returns> the total null model entropy
		/// </returns>
		public double SFPriorEntropy()
		{
			
			if (m_NoPriors)
				return System.Double.NaN;
			
			return m_SumPriorEntropy;
		}
		
		/// <summary> Returns the entropy per instance for the null model
		/// 
		/// </summary>
		/// <returns> the null model entropy per instance
		/// </returns>
		public double SFMeanPriorEntropy()
		{
			
			if (m_NoPriors)
				return System.Double.NaN;
			
			return m_SumPriorEntropy / m_WithClass;
		}
		
		/// <summary> Returns the total entropy for the scheme
		/// 
		/// </summary>
		/// <returns> the total scheme entropy
		/// </returns>
		public double SFSchemeEntropy()
		{
			
			if (m_NoPriors)
				return System.Double.NaN;
			
			return m_SumSchemeEntropy;
		}
		
		/// <summary> Returns the entropy per instance for the scheme
		/// 
		/// </summary>
		/// <returns> the scheme entropy per instance
		/// </returns>
		public double SFMeanSchemeEntropy()
		{
			
			if (m_NoPriors)
				return System.Double.NaN;
			
			return m_SumSchemeEntropy / m_WithClass;
		}
		
		/// <summary> Returns the total SF, which is the null model entropy minus
		/// the scheme entropy.
		/// 
		/// </summary>
		/// <returns> the total SF
		/// </returns>
		public double SFEntropyGain()
		{
			
			if (m_NoPriors)
				return System.Double.NaN;
			
			return m_SumPriorEntropy - m_SumSchemeEntropy;
		}
		
		/// <summary> Returns the SF per instance, which is the null model entropy
		/// minus the scheme entropy, per instance.
		/// 
		/// </summary>
		/// <returns> the SF per instance
		/// </returns>
		public double SFMeanEntropyGain()
		{
			
			if (m_NoPriors)
				return System.Double.NaN;
			
			return (m_SumPriorEntropy - m_SumSchemeEntropy) / m_WithClass;
		}
		
		/// <summary> Output the cumulative margin distribution as a string suitable
		/// for input for gnuplot or similar package.
		/// 
		/// </summary>
		/// <returns> the cumulative margin distribution
		/// </returns>
		/// <throws>  Exception if the class attribute is nominal </throws>
		public virtual System.String toCumulativeMarginDistributionString()
		{
			
			if (!m_ClassIsNominal)
			{
				throw new System.Exception("Class must be nominal for margin distributions");
			}
			System.String result = "";
			double cumulativeCount = 0;
			double margin;
			for (int i = 0; i <= k_MarginResolution; i++)
			{
				if (m_MarginCounts[i] != 0)
				{
					cumulativeCount += m_MarginCounts[i];
					margin = (double) i * 2.0 / k_MarginResolution - 1.0;
					result = result + Utils.doubleToString(margin, 7, 3) + ' ' + Utils.doubleToString(cumulativeCount * 100 / m_WithClass, 7, 3) + '\n';
				}
				else if (i == 0)
				{
					result = Utils.doubleToString(- 1.0, 7, 3) + ' ' + Utils.doubleToString(0, 7, 3) + '\n';
				}
			}
			return result;
		}
		
		
		/// <summary> Calls toSummaryString() with no title and no complexity stats
		/// 
		/// </summary>
		/// <returns> a summary description of the classifier evaluation
		/// </returns>
		public virtual System.String toSummaryString()
		{
			
			return toSummaryString("", false);
		}
		
		/// <summary> Calls toSummaryString() with a default title.
		/// 
		/// </summary>
		/// <param name="printComplexityStatistics">if true, complexity statistics are
		/// returned as well
		/// </param>
		/// <returns> the summary string
		/// </returns>
		public virtual System.String toSummaryString(bool printComplexityStatistics)
		{
			
			return toSummaryString("=== Summary ===\n", printComplexityStatistics);
		}
		
		/// <summary> Outputs the performance statistics in summary form. Lists 
		/// number (and percentage) of instances classified correctly, 
		/// incorrectly and unclassified. Outputs the total number of 
		/// instances classified, and the number of instances (if any) 
		/// that had no class value provided. 
		/// 
		/// </summary>
		/// <param name="title">the title for the statistics
		/// </param>
		/// <param name="printComplexityStatistics">if true, complexity statistics are
		/// returned as well
		/// </param>
		/// <returns> the summary as a String
		/// </returns>
		public virtual System.String toSummaryString(System.String title, bool printComplexityStatistics)
		{
			
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			
			text.Append(title + "\n");
			try
			{
				if (m_WithClass > 0)
				{
					if (m_ClassIsNominal)
					{
						
						text.Append("Correctly Classified Instances     ");
						text.Append(Utils.doubleToString(correct(), 12, 4) + "     " + Utils.doubleToString(pctCorrect(), 12, 4) + " %\n");
						text.Append("Incorrectly Classified Instances   ");
						text.Append(Utils.doubleToString(incorrect(), 12, 4) + "     " + Utils.doubleToString(pctIncorrect(), 12, 4) + " %\n");
						text.Append("Kappa statistic                    ");
						text.Append(Utils.doubleToString(kappa(), 12, 4) + "\n");
						
						if (m_CostMatrix != null)
						{
							text.Append("Total Cost                         ");
							text.Append(Utils.doubleToString(totalCost(), 12, 4) + "\n");
							text.Append("Average Cost                       ");
							text.Append(Utils.doubleToString(avgCost(), 12, 4) + "\n");
						}
						if (printComplexityStatistics)
						{
							text.Append("K&B Relative Info Score            ");
							text.Append(Utils.doubleToString(KBRelativeInformation(), 12, 4) + " %\n");
							text.Append("K&B Information Score              ");
							text.Append(Utils.doubleToString(KBInformation(), 12, 4) + " bits");
							text.Append(Utils.doubleToString(KBMeanInformation(), 12, 4) + " bits/instance\n");
						}
					}
					else
					{
						text.Append("Correlation coefficient            ");
						text.Append(Utils.doubleToString(correlationCoefficient(), 12, 4) + "\n");
					}
					if (printComplexityStatistics)
					{
						text.Append("Class complexity | order 0         ");
						text.Append(Utils.doubleToString(SFPriorEntropy(), 12, 4) + " bits");
						text.Append(Utils.doubleToString(SFMeanPriorEntropy(), 12, 4) + " bits/instance\n");
						text.Append("Class complexity | scheme          ");
						text.Append(Utils.doubleToString(SFSchemeEntropy(), 12, 4) + " bits");
						text.Append(Utils.doubleToString(SFMeanSchemeEntropy(), 12, 4) + " bits/instance\n");
						text.Append("Complexity improvement     (Sf)    ");
						text.Append(Utils.doubleToString(SFEntropyGain(), 12, 4) + " bits");
						text.Append(Utils.doubleToString(SFMeanEntropyGain(), 12, 4) + " bits/instance\n");
					}
					
					text.Append("Mean absolute error                ");
					text.Append(Utils.doubleToString(meanAbsoluteError(), 12, 4) + "\n");
					text.Append("Root mean squared error            ");
					text.Append(Utils.doubleToString(rootMeanSquaredError(), 12, 4) + "\n");
					if (!m_NoPriors)
					{
						text.Append("Relative absolute error            ");
						text.Append(Utils.doubleToString(relativeAbsoluteError(), 12, 4) + " %\n");
						text.Append("Root relative squared error        ");
						text.Append(Utils.doubleToString(rootRelativeSquaredError(), 12, 4) + " %\n");
					}
				}
				if (Utils.gr(unclassified(), 0))
				{
					text.Append("UnClassified Instances             ");
					text.Append(Utils.doubleToString(unclassified(), 12, 4) + "     " + Utils.doubleToString(pctUnclassified(), 12, 4) + " %\n");
				}
				text.Append("Total Number of Instances          ");
				text.Append(Utils.doubleToString(m_WithClass, 12, 4) + "\n");
				if (m_MissingClass > 0)
				{
					text.Append("Ignored Class Unknown Instances            ");
					text.Append(Utils.doubleToString(m_MissingClass, 12, 4) + "\n");
				}
			}
			catch (System.Exception ex)
			{
				// Should never occur since the class is known to be nominal 
				// here
				System.Console.Error.WriteLine("Arggh - Must be a bug in Evaluation class");
			}
			
			return text.ToString();
		}
		
		/// <summary> Calls toMatrixString() with a default title.
		/// 
		/// </summary>
		/// <returns> the confusion matrix as a string
		/// </returns>
		/// <throws>  Exception if the class is numeric </throws>
		public virtual System.String toMatrixString()
		{
			
			return toMatrixString("=== Confusion Matrix ===\n");
		}
		
		/// <summary> Outputs the performance statistics as a classification confusion
		/// matrix. For each class value, shows the distribution of 
		/// predicted class values.
		/// 
		/// </summary>
		/// <param name="title">the title for the confusion matrix
		/// </param>
		/// <returns> the confusion matrix as a String
		/// </returns>
		/// <throws>  Exception if the class is numeric </throws>
		public virtual System.String toMatrixString(System.String title)
		{
			
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			char[] IDChars = new char[]{'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z'};
			int IDWidth;
			bool fractional = false;
			
			if (!m_ClassIsNominal)
			{
				throw new System.Exception("Evaluation: No confusion matrix possible!");
			}
			
			// Find the maximum value in the matrix
			// and check for fractional display requirement 
			double maxval = 0;
			for (int i = 0; i < m_NumClasses; i++)
			{
				for (int j = 0; j < m_NumClasses; j++)
				{
					double current = m_ConfusionMatrix[i][j];
					if (current < 0)
					{
						current *= (- 10);
					}
					if (current > maxval)
					{
						maxval = current;
					}
					double fract = current - System.Math.Round((double) current);
					if (!fractional && ((System.Math.Log(fract) / System.Math.Log(10)) >= - 2))
					{
						fractional = true;
					}
				}
			}
			
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			IDWidth = 1 + System.Math.Max((int) (System.Math.Log(maxval) / System.Math.Log(10) + (fractional?3:0)), (int) (System.Math.Log(m_NumClasses) / System.Math.Log(IDChars.Length)));
			text.Append(title).Append("\n");
			for (int i = 0; i < m_NumClasses; i++)
			{
				if (fractional)
				{
					text.Append(" ").Append(num2ShortID(i, IDChars, IDWidth - 3)).Append("   ");
				}
				else
				{
					text.Append(" ").Append(num2ShortID(i, IDChars, IDWidth));
				}
			}
			text.Append("   <-- classified as\n");
			for (int i = 0; i < m_NumClasses; i++)
			{
				for (int j = 0; j < m_NumClasses; j++)
				{
					text.Append(" ").Append(Utils.doubleToString(m_ConfusionMatrix[i][j], IDWidth, (fractional?2:0)));
				}
				text.Append(" | ").Append(num2ShortID(i, IDChars, IDWidth)).Append(" = ").Append(m_ClassNames[i]).Append("\n");
			}
			return text.ToString();
		}
		
		/// <summary> Generates a breakdown of the accuracy for each class (with default title),
		/// incorporating various information-retrieval statistics, such as
		/// true/false positive rate, precision/recall/F-Measure.  Should be
		/// useful for ROC curves, recall/precision curves.  
		/// 
		/// </summary>
		/// <returns> the statistics presented as a string
		/// </returns>
		/// <throws>  Exception if class is not nominal </throws>
		public virtual System.String toClassDetailsString()
		{
			
			return toClassDetailsString("=== Detailed Accuracy By Class ===\n");
		}
		
		/// <summary> Generates a breakdown of the accuracy for each class,
		/// incorporating various information-retrieval statistics, such as
		/// true/false positive rate, precision/recall/F-Measure.  Should be
		/// useful for ROC curves, recall/precision curves.  
		/// 
		/// </summary>
		/// <param name="title">the title to prepend the stats string with 
		/// </param>
		/// <returns> the statistics presented as a string
		/// </returns>
		/// <throws>  Exception if class is not nominal </throws>
		public virtual System.String toClassDetailsString(System.String title)
		{
			
			if (!m_ClassIsNominal)
			{
				throw new System.Exception("Evaluation: No confusion matrix possible!");
			}
			System.Text.StringBuilder text = new System.Text.StringBuilder(title + "\nTP Rate   FP Rate" + "   Precision   Recall" + "  F-Measure   Class\n");
			for (int i = 0; i < m_NumClasses; i++)
			{
				text.Append(Utils.doubleToString(truePositiveRate(i), 7, 3)).Append("   ");
				text.Append(Utils.doubleToString(falsePositiveRate(i), 7, 3)).Append("    ");
				text.Append(Utils.doubleToString(CalculatePrecision(i), 7, 3)).Append("   ");
				text.Append(Utils.doubleToString(CalculateRecall(i), 7, 3)).Append("   ");
				text.Append(Utils.doubleToString(fMeasure(i), 7, 3)).Append("    ");
				text.Append(m_ClassNames[i]).Append('\n');
			}
			return text.ToString();
		}
		
		/// <summary> Calculate the number of true positives with respect to a particular class. 
		/// This is defined as<p/>
		/// <pre>
		/// correctly classified positives
		/// </pre>
		/// 
		/// </summary>
		/// <param name="classIndex">the index of the class to consider as "positive"
		/// </param>
		/// <returns> the true positive rate
		/// </returns>
		public virtual double numTruePositives(int classIndex)
		{
			
			double correct = 0;
			for (int j = 0; j < m_NumClasses; j++)
			{
				if (j == classIndex)
				{
					correct += m_ConfusionMatrix[classIndex][j];
				}
			}
			return correct;
		}
		
		/// <summary> Calculate the true positive rate with respect to a particular class. 
		/// This is defined as<p/>
		/// <pre>
		/// correctly classified positives
		/// ------------------------------
		/// total positives
		/// </pre>
		/// 
		/// </summary>
		/// <param name="classIndex">the index of the class to consider as "positive"
		/// </param>
		/// <returns> the true positive rate
		/// </returns>
		public virtual double truePositiveRate(int classIndex)
		{
			
			double correct = 0, total = 0;
			for (int j = 0; j < m_NumClasses; j++)
			{
				if (j == classIndex)
				{
					correct += m_ConfusionMatrix[classIndex][j];
				}
				total += m_ConfusionMatrix[classIndex][j];
			}
			if (total == 0)
			{
				return 0;
			}
			return correct / total;
		}
		
		/// <summary> Calculate the number of true negatives with respect to a particular class. 
		/// This is defined as<p/>
		/// <pre>
		/// correctly classified negatives
		/// </pre>
		/// 
		/// </summary>
		/// <param name="classIndex">the index of the class to consider as "positive"
		/// </param>
		/// <returns> the true positive rate
		/// </returns>
		public virtual double numTrueNegatives(int classIndex)
		{
			
			double correct = 0;
			for (int i = 0; i < m_NumClasses; i++)
			{
				if (i != classIndex)
				{
					for (int j = 0; j < m_NumClasses; j++)
					{
						if (j != classIndex)
						{
							correct += m_ConfusionMatrix[i][j];
						}
					}
				}
			}
			return correct;
		}
		
		/// <summary> Calculate the true negative rate with respect to a particular class. 
		/// This is defined as<p/>
		/// <pre>
		/// correctly classified negatives
		/// ------------------------------
		/// total negatives
		/// </pre>
		/// 
		/// </summary>
		/// <param name="classIndex">the index of the class to consider as "positive"
		/// </param>
		/// <returns> the true positive rate
		/// </returns>
		public virtual double trueNegativeRate(int classIndex)
		{
			
			double correct = 0, total = 0;
			for (int i = 0; i < m_NumClasses; i++)
			{
				if (i != classIndex)
				{
					for (int j = 0; j < m_NumClasses; j++)
					{
						if (j != classIndex)
						{
							correct += m_ConfusionMatrix[i][j];
						}
						total += m_ConfusionMatrix[i][j];
					}
				}
			}
			if (total == 0)
			{
				return 0;
			}
			return correct / total;
		}
		
		/// <summary> Calculate number of false positives with respect to a particular class. 
		/// This is defined as<p/>
		/// <pre>
		/// incorrectly classified negatives
		/// </pre>
		/// 
		/// </summary>
		/// <param name="classIndex">the index of the class to consider as "positive"
		/// </param>
		/// <returns> the false positive rate
		/// </returns>
		public virtual double numFalsePositives(int classIndex)
		{
			
			double incorrect = 0;
			for (int i = 0; i < m_NumClasses; i++)
			{
				if (i != classIndex)
				{
					for (int j = 0; j < m_NumClasses; j++)
					{
						if (j == classIndex)
						{
							incorrect += m_ConfusionMatrix[i][j];
						}
					}
				}
			}
			return incorrect;
		}
		
		/// <summary> Calculate the false positive rate with respect to a particular class. 
		/// This is defined as<p/>
		/// <pre>
		/// incorrectly classified negatives
		/// --------------------------------
		/// total negatives
		/// </pre>
		/// 
		/// </summary>
		/// <param name="classIndex">the index of the class to consider as "positive"
		/// </param>
		/// <returns> the false positive rate
		/// </returns>
		public virtual double falsePositiveRate(int classIndex)
		{
			
			double incorrect = 0, total = 0;
			for (int i = 0; i < m_NumClasses; i++)
			{
				if (i != classIndex)
				{
					for (int j = 0; j < m_NumClasses; j++)
					{
						if (j == classIndex)
						{
							incorrect += m_ConfusionMatrix[i][j];
						}
						total += m_ConfusionMatrix[i][j];
					}
				}
			}
			if (total == 0)
			{
				return 0;
			}
			return incorrect / total;
		}
		
		/// <summary> Calculate number of false negatives with respect to a particular class. 
		/// This is defined as<p/>
		/// <pre>
		/// incorrectly classified positives
		/// </pre>
		/// 
		/// </summary>
		/// <param name="classIndex">the index of the class to consider as "positive"
		/// </param>
		/// <returns> the false positive rate
		/// </returns>
		public virtual double numFalseNegatives(int classIndex)
		{
			
			double incorrect = 0;
			for (int i = 0; i < m_NumClasses; i++)
			{
				if (i == classIndex)
				{
					for (int j = 0; j < m_NumClasses; j++)
					{
						if (j != classIndex)
						{
							incorrect += m_ConfusionMatrix[i][j];
						}
					}
				}
			}
			return incorrect;
		}
		
		/// <summary> Calculate the false negative rate with respect to a particular class. 
		/// This is defined as<p/>
		/// <pre>
		/// incorrectly classified positives
		/// --------------------------------
		/// total positives
		/// </pre>
		/// 
		/// </summary>
		/// <param name="classIndex">the index of the class to consider as "positive"
		/// </param>
		/// <returns> the false positive rate
		/// </returns>
		public virtual double falseNegativeRate(int classIndex)
		{
			
			double incorrect = 0, total = 0;
			for (int i = 0; i < m_NumClasses; i++)
			{
				if (i == classIndex)
				{
					for (int j = 0; j < m_NumClasses; j++)
					{
						if (j != classIndex)
						{
							incorrect += m_ConfusionMatrix[i][j];
						}
						total += m_ConfusionMatrix[i][j];
					}
				}
			}
			if (total == 0)
			{
				return 0;
			}
			return incorrect / total;
		}
		
		/// <summary> Calculate the recall with respect to a particular class. 
		/// This is defined as<p/>
		/// <pre>
		/// correctly classified positives
		/// ------------------------------
		/// total positives
		/// </pre><p/>
		/// (Which is also the same as the truePositiveRate.)
		/// 
		/// </summary>
		/// <param name="classIndex">the index of the class to consider as "positive"
		/// </param>
		/// <returns> the recall
		/// </returns>
		public virtual double CalculateRecall(int classIndex)
		{
			
			return truePositiveRate(classIndex);
		}
		
		/// <summary> Calculate the precision with respect to a particular class. 
		/// This is defined as<p/>
		/// <pre>
		/// correctly classified positives
		/// ------------------------------
		/// total predicted as positive
		/// </pre>
		/// 
		/// </summary>
		/// <param name="classIndex">the index of the class to consider as "positive"
		/// </param>
		/// <returns> the precision
		/// </returns>
		public virtual double CalculatePrecision(int classIndex)
		{
			
			double correct = 0, total = 0;
			for (int i = 0; i < m_NumClasses; i++)
			{
				if (i == classIndex)
				{
					correct += m_ConfusionMatrix[i][classIndex];
				}
				total += m_ConfusionMatrix[i][classIndex];
			}
			if (total == 0)
			{
				return 0;
			}
			return correct / total;
		}
		
		/// <summary> Calculate the F-Measure with respect to a particular class. 
		/// This is defined as<p/>
		/// <pre>
		/// 2 * recall * precision
		/// ----------------------
		/// recall + precision
		/// </pre>
		/// 
		/// </summary>
		/// <param name="classIndex">the index of the class to consider as "positive"
		/// </param>
		/// <returns> the F-Measure
		/// </returns>
		public virtual double fMeasure(int classIndex)
		{

            double precision = CalculatePrecision(classIndex);
			double recall = CalculateRecall(classIndex);
			if ((precision + recall) == 0)
			{
				return 0;
			}
			return 2 * precision * recall / (precision + recall);
		}
		
		/// <summary> Updates the class prior probabilities (when incrementally 
		/// training)
		/// 
		/// </summary>
		/// <param name="instance">the new training instance seen
		/// </param>
		/// <throws>  Exception if the class of the instance is not </throws>
		/// <summary> set
		/// </summary>
		public virtual void  updatePriors(Instance instance)
		{
			if (!instance.classIsMissing())
			{
				if (!m_ClassIsNominal)
				{
					if (!instance.classIsMissing())
					{
						addNumericTrainClass(instance.classValue(), instance.weight());
					}
				}
				else
				{
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					m_ClassPriors[(int) instance.classValue()] += instance.weight();
					m_ClassPriorsSum += instance.weight();
				}
			}
		}
		
		/// <summary> disables the use of priors, e.g., in case of de-serialized schemes
		/// that have no access to the original training set, but are evaluated
		/// on a set set.
		/// </summary>
		public virtual void  useNoPriors()
		{
			m_NoPriors = true;
		}
		
		/// <summary> Tests whether the current evaluation object is equal to another
		/// evaluation object
		/// 
		/// </summary>
		/// <param name="obj">the object to compare against
		/// </param>
		/// <returns> true if the two objects are equal
		/// </returns>
		public  override bool Equals(System.Object obj)
		{
			
			if ((obj == null) || !(obj.GetType().Equals(this.GetType())))
			{
				return false;
			}
			Evaluation cmp = (Evaluation) obj;
			if (m_ClassIsNominal != cmp.m_ClassIsNominal)
				return false;
			if (m_NumClasses != cmp.m_NumClasses)
				return false;
			
			if (m_Incorrect != cmp.m_Incorrect)
				return false;
			if (m_Correct != cmp.m_Correct)
				return false;
			if (m_Unclassified != cmp.m_Unclassified)
				return false;
			if (m_MissingClass != cmp.m_MissingClass)
				return false;
			if (m_WithClass != cmp.m_WithClass)
				return false;
			
			if (m_SumErr != cmp.m_SumErr)
				return false;
			if (m_SumAbsErr != cmp.m_SumAbsErr)
				return false;
			if (m_SumSqrErr != cmp.m_SumSqrErr)
				return false;
			if (m_SumClass != cmp.m_SumClass)
				return false;
			if (m_SumSqrClass != cmp.m_SumSqrClass)
				return false;
			if (m_SumPredicted != cmp.m_SumPredicted)
				return false;
			if (m_SumSqrPredicted != cmp.m_SumSqrPredicted)
				return false;
			if (m_SumClassPredicted != cmp.m_SumClassPredicted)
				return false;
			
			if (m_ClassIsNominal)
			{
				for (int i = 0; i < m_NumClasses; i++)
				{
					for (int j = 0; j < m_NumClasses; j++)
					{
						if (m_ConfusionMatrix[i][j] != cmp.m_ConfusionMatrix[i][j])
						{
							return false;
						}
					}
				}
			}
			
			return true;
		}
		
		/// <summary> Prints the predictions for the given dataset into a String variable.
		/// 
		/// </summary>
		/// <param name="classifier		the">classifier to use
		/// </param>
		/// <param name="train		the">training data
		/// </param>
		/// <param name="testFileName	the">name of the test file
		/// </param>
		/// <param name="classIndex		the">class index
		/// </param>
		/// <param name="attributesToOutput	the">indices of the attributes to output
		/// </param>
		/// <returns>			the generated predictions for the attribute range
		/// </returns>
		/// <throws>  Exception 		if test file cannot be opened </throws>
		protected internal static System.String toPrintClassifications(Classifier classifier, Instances train, System.String testFileName, int classIndex, Range attributesToOutput)
		{
			
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			if (testFileName.Length != 0)
			{
				System.IO.StreamReader testReader = null;
				try
				{
					//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.io.BufferedReader.BufferedReader'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
					//UPGRADE_WARNING: At least one expression was used more than once in the target code. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1181'"
					//UPGRADE_TODO: Constructor 'java.io.FileReader.FileReader' was converted to 'System.IO.StreamReader' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073'"
					testReader = new System.IO.StreamReader(new System.IO.StreamReader(testFileName, System.Text.Encoding.Default).BaseStream, new System.IO.StreamReader(testFileName, System.Text.Encoding.Default).CurrentEncoding);
				}
				catch (System.Exception e)
				{
					//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Throwable.getMessage' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
					throw new System.Exception("Can't open file " + e.Message + '.');
				}
				Instances test = new Instances(testReader, 1);
				if (classIndex != - 1)
				{
					test.ClassIndex = classIndex - 1;
				}
				else
				{
					test.ClassIndex = test.numAttributes() - 1;
				}
				int i = 0;
				while (test.readInstance(testReader))
				{
					Instance instance = test.instance(0);
					Instance withMissing = (Instance) instance.copy();
					withMissing.Dataset = test;
					double predValue = ((Classifier) classifier).classifyInstance(withMissing);
					if (test.classAttribute().Numeric)
					{
						if (Instance.isMissingValue(predValue))
						{
							text.Append(i + " missing ");
						}
						else
						{
							text.Append(i + " " + predValue + " ");
						}
						if (instance.classIsMissing())
						{
							text.Append("missing");
						}
						else
						{
							text.Append(instance.classValue());
						}
						text.Append(" " + attributeValuesString(withMissing, attributesToOutput) + "\n");
					}
					else
					{
						if (Instance.isMissingValue(predValue))
						{
							text.Append(i + " missing ");
						}
						else
						{
							//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
							text.Append(i + " " + test.classAttribute().value_Renamed((int) predValue) + " ");
						}
						if (Instance.isMissingValue(predValue))
						{
							text.Append("missing ");
						}
						else
						{
							//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
							text.Append(classifier.distributionForInstance(withMissing)[(int) predValue] + " ");
						}
						text.Append(instance.toString(instance.classIndex()) + " " + attributeValuesString(withMissing, attributesToOutput) + "\n");
					}
					test.delete(0);
					i++;
				}
				testReader.Close();
			}
			return text.ToString();
		}
		
		/// <summary> Builds a string listing the attribute values in a specified range of indices,
		/// separated by commas and enclosed in brackets.
		/// 
		/// </summary>
		/// <param name="instance">the instance to print the values from
		/// </param>
		/// <param name="attRange">the range of the attributes to list
		/// </param>
		/// <returns> a string listing values of the attributes in the range
		/// </returns>
		protected internal static System.String attributeValuesString(Instance instance, Range attRange)
		{
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			if (attRange != null)
			{
				bool firstOutput = true;
				attRange.Upper = instance.numAttributes() - 1;
				for (int i = 0; i < instance.numAttributes(); i++)
					if (attRange.isInRange(i) && i != instance.classIndex())
					{
						if (firstOutput)
							text.Append("(");
						else
							text.Append(",");
						text.Append(instance.toString(i));
						firstOutput = false;
					}
				if (!firstOutput)
					text.Append(")");
			}
			return text.ToString();
		}
		
		/// <summary> Make up the help string giving all the command line options
		/// 
		/// </summary>
		/// <param name="classifier">the classifier to include options for
		/// </param>
		/// <returns> a string detailing the valid command line options
		/// </returns>
		protected internal static System.String makeOptionString(Classifier classifier)
		{
			
			System.Text.StringBuilder optionsText = new System.Text.StringBuilder("");
			
			// General options
			optionsText.Append("\n\nGeneral options:\n\n");
			optionsText.Append("-t <name of training file>\n");
			optionsText.Append("\tSets training file.\n");
			optionsText.Append("-T <name of test file>\n");
			optionsText.Append("\tSets test file. If missing, a cross-validation");
			optionsText.Append(" will be performed on the training data.\n");
			optionsText.Append("-c <class index>\n");
			optionsText.Append("\tSets index of class attribute (default: last).\n");
			optionsText.Append("-x <number of folds>\n");
			optionsText.Append("\tSets number of folds for cross-validation (default: 10).\n");
			optionsText.Append("-s <random number seed>\n");
			optionsText.Append("\tSets random number seed for cross-validation (default: 1).\n");
			optionsText.Append("-m <name of file with cost matrix>\n");
			optionsText.Append("\tSets file with cost matrix.\n");
			optionsText.Append("-l <name of input file>\n");
			optionsText.Append("\tSets model input file.\n");
			optionsText.Append("-d <name of output file>\n");
			optionsText.Append("\tSets model output file.\n");
			optionsText.Append("-v\n");
			optionsText.Append("\tOutputs no statistics for training data.\n");
			optionsText.Append("-o\n");
			optionsText.Append("\tOutputs statistics only, not the classifier.\n");
			optionsText.Append("-i\n");
			optionsText.Append("\tOutputs detailed information-retrieval");
			optionsText.Append(" statistics for each class.\n");
			optionsText.Append("-k\n");
			optionsText.Append("\tOutputs information-theoretic statistics.\n");
			optionsText.Append("-p <attribute range>\n");
			optionsText.Append("\tOnly outputs predictions for test instances, along with attributes " + "(0 for none).\n");
			optionsText.Append("-r\n");
			optionsText.Append("\tOnly outputs cumulative margin distribution.\n");
			if (classifier is Sourcable)
			{
				optionsText.Append("-z <class name>\n");
				optionsText.Append("\tOnly outputs the source representation" + " of the classifier, giving it the supplied" + " name.\n");
			}
			if (classifier is Drawable)
			{
				optionsText.Append("-g\n");
				optionsText.Append("\tOnly outputs the graph representation" + " of the classifier.\n");
			}
			
			// Get scheme-specific options
			//		if (classifier instanceof OptionHandler) 
			//		{
			//			optionsText.append("\nOptions specific to "
			//				+ classifier.getClass().getName()
			//				+ ":\n\n");
			//			Enumeration enu = ((OptionHandler)classifier).listOptions();
			//			while (enu.hasMoreElements()) 
			//			{
			//				Option option = (Option) enu.nextElement();
			//				optionsText.append(option.synopsis() + '\n');
			//				optionsText.append(option.description() + "\n");
			//			}
			//		}
			return optionsText.ToString();
		}
		
		
		/// <summary> Method for generating indices for the confusion matrix.
		/// 
		/// </summary>
		/// <param name="num">	integer to format
		/// </param>
		/// <param name="IDChars	the">characters to use
		/// </param>
		/// <param name="IDWidth	the">width of the entry
		/// </param>
		/// <returns> 		the formatted integer as a string
		/// </returns>
		protected internal virtual System.String num2ShortID(int num, char[] IDChars, int IDWidth)
		{
			
			char[] ID = new char[IDWidth];
			int i;
			
			for (i = IDWidth - 1; i >= 0; i--)
			{
				ID[i] = IDChars[num % IDChars.Length];
				num = num / IDChars.Length - 1;
				if (num < 0)
				{
					break;
				}
			}
			for (i--; i >= 0; i--)
			{
				ID[i] = ' ';
			}
			
			return new System.String(ID);
		}
		
		
		/// <summary> Convert a single prediction into a probability distribution
		/// with all zero probabilities except the predicted value which
		/// has probability 1.0;
		/// 
		/// </summary>
		/// <param name="predictedClass">the index of the predicted class
		/// </param>
		/// <returns> the probability distribution
		/// </returns>
		protected internal virtual double[] makeDistribution(double predictedClass)
		{
			
			double[] result = new double[m_NumClasses];
			if (Instance.isMissingValue(predictedClass))
			{
				return result;
			}
			if (m_ClassIsNominal)
			{
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				result[(int) predictedClass] = 1.0;
			}
			else
			{
				result[0] = predictedClass;
			}
			return result;
		}
		
		/// <summary> Updates all the statistics about a classifiers performance for 
		/// the current test instance.
		/// 
		/// </summary>
		/// <param name="predictedDistribution">the probabilities assigned to 
		/// each class
		/// </param>
		/// <param name="instance">the instance to be classified
		/// </param>
		/// <throws>  Exception if the class of the instance is not </throws>
		/// <summary> set
		/// </summary>
		protected internal virtual void  updateStatsForClassifier(double[] predictedDistribution, Instance instance)
		{
			
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			int actualClass = (int) instance.classValue();
			
			if (!instance.classIsMissing())
			{
				updateMargins(predictedDistribution, actualClass, instance.weight());
				
				// Determine the predicted class (doesn't detect multiple 
				// classifications)
				int predictedClass = - 1;
				double bestProb = 0.0;
				for (int i = 0; i < m_NumClasses; i++)
				{
					if (predictedDistribution[i] > bestProb)
					{
						predictedClass = i;
						bestProb = predictedDistribution[i];
					}
				}
				
				m_WithClass += instance.weight();
				
				// Determine misclassification cost
				if (m_CostMatrix != null)
				{
					if (predictedClass < 0)
					{
						// For missing predictions, we assume the worst possible cost.
						// This is pretty harsh.
						// Perhaps we could take the negative of the cost of a correct
						// prediction (-m_CostMatrix.getXmlElement(actualClass,actualClass)),
						// although often this will be zero
						m_TotalCost += instance.weight() * m_CostMatrix.getMaxCost(actualClass);
					}
					else
					{
						m_TotalCost += instance.weight() * m_CostMatrix.getXmlElement(actualClass, predictedClass);
					}
				}
				
				// Update counts when no class was predicted
				if (predictedClass < 0)
				{
					m_Unclassified += instance.weight();
					return ;
				}
				
				double predictedProb = System.Math.Max(MIN_SF_PROB, predictedDistribution[actualClass]);
				double priorProb = System.Math.Max(MIN_SF_PROB, m_ClassPriors[actualClass] / m_ClassPriorsSum);
				if (predictedProb >= priorProb)
				{
					m_SumKBInfo += (Utils.log2(predictedProb) - Utils.log2(priorProb)) * instance.weight();
				}
				else
				{
					m_SumKBInfo -= (Utils.log2(1.0 - predictedProb) - Utils.log2(1.0 - priorProb)) * instance.weight();
				}
				
				m_SumSchemeEntropy -= Utils.log2(predictedProb) * instance.weight();
				m_SumPriorEntropy -= Utils.log2(priorProb) * instance.weight();
				
				updateNumericScores(predictedDistribution, makeDistribution(instance.classValue()), instance.weight());
				
				// Update other stats
				m_ConfusionMatrix[actualClass][predictedClass] += instance.weight();
				if (predictedClass != actualClass)
				{
					m_Incorrect += instance.weight();
				}
				else
				{
					m_Correct += instance.weight();
				}
			}
			else
			{
				m_MissingClass += instance.weight();
			}
		}
		
		/// <summary> Updates all the statistics about a predictors performance for 
		/// the current test instance.
		/// 
		/// </summary>
		/// <param name="predictedValue">the numeric value the classifier predicts
		/// </param>
		/// <param name="instance">the instance to be classified
		/// </param>
		/// <throws>  Exception if the class of the instance is not </throws>
		/// <summary> set
		/// </summary>
		protected internal virtual void  updateStatsForPredictor(double predictedValue, Instance instance)
		{
			
			if (!instance.classIsMissing())
			{
				
				// Update stats
				m_WithClass += instance.weight();
				if (Instance.isMissingValue(predictedValue))
				{
					m_Unclassified += instance.weight();
					return ;
				}
				m_SumClass += instance.weight() * instance.classValue();
				m_SumSqrClass += instance.weight() * instance.classValue() * instance.classValue();
				m_SumClassPredicted += instance.weight() * instance.classValue() * predictedValue;
				m_SumPredicted += instance.weight() * predictedValue;
				m_SumSqrPredicted += instance.weight() * predictedValue * predictedValue;
				
				if (m_ErrorEstimator == null)
				{
					setNumericPriorsFromBuffer();
				}
				double predictedProb = Math.Max(m_ErrorEstimator.getProbability(predictedValue - instance.classValue()), MIN_SF_PROB);
				double priorProb = Math.Max(m_PriorErrorEstimator.getProbability(instance.classValue()), MIN_SF_PROB);
				
				m_SumSchemeEntropy -= Utils.log2(predictedProb) * instance.weight();
				m_SumPriorEntropy -= Utils.log2(priorProb) * instance.weight();
				m_ErrorEstimator.addValue(predictedValue - instance.classValue(), instance.weight());
				
				updateNumericScores(makeDistribution(predictedValue), makeDistribution(instance.classValue()), instance.weight());
			}
			else
				m_MissingClass += instance.weight();
		}
		
		/// <summary> Update the cumulative record of classification margins
		/// 
		/// </summary>
		/// <param name="predictedDistribution">the probability distribution predicted for
		/// the current instance
		/// </param>
		/// <param name="actualClass">the index of the actual instance class
		/// </param>
		/// <param name="weight">the weight assigned to the instance
		/// </param>
		protected internal virtual void  updateMargins(double[] predictedDistribution, int actualClass, double weight)
		{
			
			double probActual = predictedDistribution[actualClass];
			double probNext = 0;
			
			for (int i = 0; i < m_NumClasses; i++)
				if ((i != actualClass) && (predictedDistribution[i] > probNext))
					probNext = predictedDistribution[i];
			
			double margin = probActual - probNext;
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			int bin = (int) ((margin + 1.0) / 2.0 * k_MarginResolution);
			m_MarginCounts[bin] += weight;
		}
		
		/// <summary> Update the numeric accuracy measures. For numeric classes, the
		/// accuracy is between the actual and predicted class values. For 
		/// nominal classes, the accuracy is between the actual and 
		/// predicted class probabilities.
		/// 
		/// </summary>
		/// <param name="predicted">the predicted values
		/// </param>
		/// <param name="actual">the actual value
		/// </param>
		/// <param name="weight">the weight associated with this prediction
		/// </param>
		protected internal virtual void  updateNumericScores(double[] predicted, double[] actual, double weight)
		{
			
			double diff;
			double sumErr = 0, sumAbsErr = 0, sumSqrErr = 0;
			double sumPriorAbsErr = 0, sumPriorSqrErr = 0;
			for (int i = 0; i < m_NumClasses; i++)
			{
				diff = predicted[i] - actual[i];
				sumErr += diff;
				sumAbsErr += System.Math.Abs(diff);
				sumSqrErr += diff * diff;
				diff = (m_ClassPriors[i] / m_ClassPriorsSum) - actual[i];
				sumPriorAbsErr += System.Math.Abs(diff);
				sumPriorSqrErr += diff * diff;
			}
			m_SumErr += weight * sumErr / m_NumClasses;
			m_SumAbsErr += weight * sumAbsErr / m_NumClasses;
			m_SumSqrErr += weight * sumSqrErr / m_NumClasses;
			m_SumPriorAbsErr += weight * sumPriorAbsErr / m_NumClasses;
			m_SumPriorSqrErr += weight * sumPriorSqrErr / m_NumClasses;
		}
		
		/// <summary> Adds a numeric (non-missing) training class value and weight to 
		/// the buffer of stored values.
		/// 
		/// </summary>
		/// <param name="classValue">the class value
		/// </param>
		/// <param name="weight">the instance weight
		/// </param>
		protected internal virtual void  addNumericTrainClass(double classValue, double weight)
		{
			
			if (m_TrainClassVals == null)
			{
				m_TrainClassVals = new double[100];
				m_TrainClassWeights = new double[100];
			}
			if (m_NumTrainClassVals == m_TrainClassVals.Length)
			{
				double[] temp = new double[m_TrainClassVals.Length * 2];
				Array.Copy(m_TrainClassVals, 0, temp, 0, m_TrainClassVals.Length);
				m_TrainClassVals = temp;
				
				temp = new double[m_TrainClassWeights.Length * 2];
				Array.Copy(m_TrainClassWeights, 0, temp, 0, m_TrainClassWeights.Length);
				m_TrainClassWeights = temp;
			}
			m_TrainClassVals[m_NumTrainClassVals] = classValue;
			m_TrainClassWeights[m_NumTrainClassVals] = weight;
			m_NumTrainClassVals++;
		}
		
		/// <summary> Sets up the priors for numeric class attributes from the 
		/// training class values that have been seen so far.
		/// </summary>
		protected internal virtual void  setNumericPriorsFromBuffer()
		{
			
			double numPrecision = 0.01; // Default value
			if (m_NumTrainClassVals > 1)
			{
				double[] temp = new double[m_NumTrainClassVals];
				Array.Copy(m_TrainClassVals, 0, temp, 0, m_NumTrainClassVals);
				int[] index = Utils.sort(temp);
				double lastVal = temp[index[0]];
				double deltaSum = 0;
				int distinct = 0;
				for (int i = 1; i < temp.Length; i++)
				{
					double current = temp[index[i]];
					if (current != lastVal)
					{
						deltaSum += current - lastVal;
						lastVal = current;
						distinct++;
					}
				}
				if (distinct > 0)
				{
					numPrecision = deltaSum / distinct;
				}
			}
			m_PriorErrorEstimator = new KernelEstimator(numPrecision);
			m_ErrorEstimator = new KernelEstimator(numPrecision);
			m_ClassPriors[0] = m_ClassPriorsSum = 0;
			for (int i = 0; i < m_NumTrainClassVals; i++)
			{
				m_ClassPriors[0] += m_TrainClassVals[i] * m_TrainClassWeights[i];
				m_ClassPriorsSum += m_TrainClassWeights[i];
				m_PriorErrorEstimator.addValue(m_TrainClassVals[i], m_TrainClassWeights[i]);
			}
		}
		//UPGRADE_NOTE: The following method implementation was automatically added to preserve functionality. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1306'"
		public override int GetHashCode()
		{
			return base.GetHashCode();
		}
	}
}