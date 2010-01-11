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
*    ClassifierSubsetEval.java
*    Copyright (C) 2000 Mark Hall
*
*/
using System;
//UPGRADE_TODO: The package 'weka.core' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using weka.core;
//UPGRADE_TODO: The package 'weka.classifiers' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using weka.classifiers;
//UPGRADE_TODO: The type 'weka.classifiers.rules.ZeroR' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using ZeroR = weka.classifiers.rules.ZeroR;
//UPGRADE_TODO: The type 'weka.classifiers.Evaluation' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using Evaluation = weka.classifiers.Evaluation;
//UPGRADE_TODO: The type 'weka.filters.Filter' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using Filter = weka.filters.Filter;
//UPGRADE_TODO: The type 'weka.filters.unsupervised.attribute.Remove' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using Remove = weka.filters.unsupervised.attribute.Remove;
namespace weka.attributeSelection
{
	
	
	/// <summary> Classifier subset evaluator. Uses a classifier to estimate the "merit"
	/// of a set of attributes.
	/// 
	/// Valid options are:<p>
	/// 
	/// -B <classifier> <br>
	/// Class name of the classifier to use for accuracy estimation.
	/// Place any classifier options last on the command line following a
	/// "--". Eg  -B weka.classifiers.bayes.NaiveBayes ... -- -K <p>
	/// 
	/// -T <br>
	/// Use the training data for accuracy estimation rather than a hold out/
	/// test set. <p>
	/// 
	/// -H <filename> <br>
	/// The file containing hold out/test instances to use for accuracy estimation
	/// <p>
	/// 
	/// </summary>
	/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.12.2.1 $
	/// </version>
	[Serializable]
	public class ClassifierSubsetEval:HoldOutSubsetEvaluator, OptionHandler, ErrorBasedMeritEvaluator
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the current settings of ClassifierSubsetEval
		/// 
		/// </summary>
		/// <returns> an array of strings suitable for passing to setOptions()
		/// </returns>
		/// <summary> Parses a given list of options.
		/// 
		/// Valid options are:<p>
		/// 
		/// -C <classifier> <br>
		/// Class name of classifier to use for accuracy estimation.
		/// Place any classifier options last on the command line following a
		/// "--". Eg  -B weka.classifiers.bayes.NaiveBayes ... -- -K <p>
		/// 
		/// -T <br>
		/// Use training data instead of a hold out/test set for accuracy estimation.
		/// <p>
		/// 
		/// -H <filname> <br>
		/// Name of the hold out/test set to estimate classifier accuracy on.
		/// <p>
		/// 
		/// </summary>
		/// <param name="options">the list of options as an array of strings
		/// </param>
		/// <exception cref="Exception">if an option is not supported
		/// 
		/// 
		/// </exception>
		virtual public System.String[] Options
		{
			get
			{
				System.String[] classifierOptions = new System.String[0];
				
				if ((m_Classifier != null) && (m_Classifier is OptionHandler))
				{
					classifierOptions = ((OptionHandler) m_Classifier).Options;
				}
				
				System.String[] options = new System.String[6 + classifierOptions.Length];
				int current = 0;
				
				if (Classifier != null)
				{
					options[current++] = "-B";
                    options[current++] = Classifier.GetType().ToString();
				}
				
				if (UseTraining)
				{
					options[current++] = "-T";
				}
				options[current++] = "-H"; options[current++] = HoldOutFile.FullName;
				options[current++] = "--";
				Array.Copy(classifierOptions, 0, options, current, classifierOptions.Length);
				current += classifierOptions.Length;
				while (current < options.Length)
				{
					options[current++] = "";
				}
				
				return options;
			}
			
			set
			{
				System.String optionString;
				resetOptions();
				
				optionString = Utils.getOption('B', value);
				
				if (optionString.Length == 0)
				{
					throw new System.Exception("A classifier must be specified with -B option");
				}
				
				Classifier = Classifier.forName(optionString, Utils.partitionOptions(value));
				
				optionString = Utils.getOption('H', value);
				if (optionString.Length != 0)
				{
					HoldOutFile = new System.IO.FileInfo(optionString);
				}
				
				UseTraining = Utils.getFlag('T', value);
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Get the classifier used as the base learner.
		/// 
		/// </summary>
		/// <returns> the classifier used as the classifier
		/// </returns>
		/// <summary> Set the classifier to use for accuracy estimation
		/// 
		/// </summary>
		/// <param name="newClassifier">the Classifier to use.
		/// </param>
		virtual public Classifier Classifier
		{
			get
			{
				return m_Classifier;
			}
			
			set
			{
				m_Classifier = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the file that holds hold out/test instances.</summary>
		/// <returns> File that contains hold out instances
		/// </returns>
		/// <summary> Set the file that contains hold out/test instances</summary>
		/// <param name="h">the hold out file
		/// </param>
		virtual public System.IO.FileInfo HoldOutFile
		{
			get
			{
				return m_holdOutFile;
			}
			
			set
			{
				m_holdOutFile = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Get if training data is to be used instead of hold out/test data</summary>
		/// <returns> true if training data is to be used instead of hold out data
		/// </returns>
		/// <summary> Set if training data is to be used instead of hold out/test data</summary>
		/// <returns> true if training data is to be used instead of hold out data
		/// </returns>
		virtual public bool UseTraining
		{
			get
			{
				return m_useTraining;
			}
			
			set
			{
				m_useTraining = value;
			}
			
		}
		
		/// <summary>training instances </summary>
		private Instances m_trainingInstances;
		
		/// <summary>class index </summary>
		private int m_classIndex;
		
		/// <summary>number of attributes in the training data </summary>
		private int m_numAttribs;
		
		/// <summary>number of training instances </summary>
		private int m_numInstances;
		
		/// <summary>holds the classifier to use for error estimates </summary>
		private Classifier m_Classifier = new ZeroR();
		
		/// <summary>holds the evaluation object to use for evaluating the classifier </summary>
		private Evaluation m_Evaluation;
		
		/// <summary>the file that containts hold out/test instances </summary>
		private System.IO.FileInfo m_holdOutFile = new System.IO.FileInfo("Click to set hold out or " + "test instances");
		
		/// <summary>the instances to test on </summary>
		private Instances m_holdOutInstances = null;
		
		/// <summary>evaluate on training data rather than seperate hold out/test set </summary>
		private bool m_useTraining = true;
		
		/// <summary> Returns a string describing this attribute evaluator</summary>
		/// <returns> a description of the evaluator suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String globalInfo()
		{
			return "Evaluates attribute subsets on training data or a seperate " + "hold out testing set";
		}
		
		/// <summary> Returns an enumeration describing the available options. <p>
		/// 
		/// -B <classifier> <br>
		/// Class name of the classifier to use for accuracy estimation.
		/// Place any classifier options last on the command line following a
		/// "--". Eg  -B weka.classifiers.bayes.NaiveBayes ... -- -K <p>
		/// 
		/// -T <br>
		/// Use the training data for accuracy estimation rather than a hold out/
		/// test set. <p>
		/// 
		/// -H <filename> <br>
		/// The file containing hold out/test instances to use for accuracy estimation
		/// <p>
		/// 
		/// </summary>
		/// <returns> an enumeration of all the available options.
		/// 
		/// </returns>
		public virtual System.Collections.IEnumerator listOptions()
		{
			System.Collections.ArrayList newVector = System.Collections.ArrayList.Synchronized(new System.Collections.ArrayList(3));
			newVector.Add(new Option("\tclass name of the classifier to use for" + "\n\taccuracy estimation. Place any" + "\n\tclassifier options LAST on the" + "\n\tcommand line following a \"--\"." + "\n\teg. -C weka.classifiers.bayes.NaiveBayes ... " + "-- -K", "B", 1, "-B <classifier>"));
			
			newVector.Add(new Option("\tUse the training data to estimate" + " accuracy.", "T", 0, "-T"));
			
			newVector.Add(new Option("\tName of the hold out/test set to " + "\n\testimate accuracy on.", "H", 1, "-H <filename>"));
			
			if ((m_Classifier != null) && (m_Classifier is OptionHandler))
			{
                newVector.Add(new Option("", "", 0, "\nOptions specific to " + "scheme " + m_Classifier.GetType().ToString() + ":"));
				System.Collections.IEnumerator enu = ((OptionHandler) m_Classifier).listOptions();
				
				//UPGRADE_TODO: Method 'java.util.Enumeration.hasMoreElements' was converted to 'System.Collections.IEnumerator.MoveNext' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationhasMoreElements'"
				while (enu.MoveNext())
				{
					//UPGRADE_TODO: Method 'java.util.Enumeration.nextElement' was converted to 'System.Collections.IEnumerator.Current' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationnextElement'"
					newVector.Add(enu.Current);
				}
			}
			
			return newVector.GetEnumerator();
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String classifierTipText()
		{
			return "Classifier to use for estimating the accuracy of subsets";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String holdOutFileTipText()
		{
			return "File containing hold out/test instances.";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String useTrainingTipText()
		{
			return "Use training data instead of hold out/test instances.";
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
			
			m_trainingInstances = data;
			m_classIndex = m_trainingInstances.classIndex();
			m_numAttribs = m_trainingInstances.numAttributes();
			m_numInstances = m_trainingInstances.numInstances();
			
			// load the testing data
			if (!m_useTraining && (!HoldOutFile.FullName.StartsWith("Click to set")))
			{
				//UPGRADE_ISSUE: Class hierarchy differences between 'java.io.Reader' and 'System.IO.StreamReader' may cause compilation errors. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1186'"
				//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.io.BufferedReader.BufferedReader'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
				//UPGRADE_WARNING: At least one expression was used more than once in the target code. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1181'"
				//UPGRADE_TODO: Constructor 'java.io.FileReader.FileReader' was converted to 'System.IO.StreamReader' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073'"
				System.IO.StreamReader r = new System.IO.StreamReader(new System.IO.StreamReader(HoldOutFile.FullName, System.Text.Encoding.Default).BaseStream, new System.IO.StreamReader(HoldOutFile.FullName, System.Text.Encoding.Default).CurrentEncoding);
				m_holdOutInstances = new Instances(r);
				m_holdOutInstances.ClassIndex=m_trainingInstances.classIndex();
				if (m_trainingInstances.equalHeaders(m_holdOutInstances) == false)
				{
					throw new System.Exception("Hold out/test set is not compatable with " + "training data.");
				}
			}
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
			int i, j;
			double errorRate = 0;
			int numAttributes = 0;
			Instances trainCopy = null;
			Instances testCopy = null;
			
			Remove delTransform = new Remove();
			delTransform.set_InvertSelection(true);
			// copy the training instances
			trainCopy = new Instances(m_trainingInstances);
			
			if (!m_useTraining)
			{
				if (m_holdOutInstances == null)
				{
					throw new System.Exception("Must specify a set of hold out/test instances " + "with -H");
				}
				// copy the test instances
				testCopy = new Instances(m_holdOutInstances);
			}
			
			// count attributes set in the BitSet
			for (i = 0; i < m_numAttribs; i++)
			{
				if (subset.Get(i))
				{
					numAttributes++;
				}
			}
			
			// set up an array of attribute indexes for the filter (+1 for the class)
			int[] featArray = new int[numAttributes + 1];
			
			for (i = 0, j = 0; i < m_numAttribs; i++)
			{
				if (subset.Get(i))
				{
					featArray[j++] = i;
				}
			}
			
			featArray[j] = m_classIndex;
			delTransform.SetAttributeIndicesArray(featArray);
			delTransform.setInputFormat(trainCopy);
			trainCopy = Filter.useFilter(trainCopy, delTransform);
			if (!m_useTraining)
			{
				testCopy = Filter.useFilter(testCopy, delTransform);
			}
			
			// build the classifier
			m_Classifier.buildClassifier(trainCopy);
			
			m_Evaluation = new Evaluation(trainCopy);
			if (!m_useTraining)
			{
				m_Evaluation.evaluateModel(m_Classifier, testCopy);
			}
			else
			{
				m_Evaluation.evaluateModel(m_Classifier, trainCopy);
			}
			
			if (m_trainingInstances.classAttribute().Nominal)
			{
				errorRate = m_Evaluation.errorRate();
			}
			else
			{
				errorRate = m_Evaluation.meanAbsoluteError();
			}
			
			m_Evaluation = null;
			// return the negative of the error rate as search methods  need to
			// maximize something
			return - errorRate;
		}
		
		/// <summary> Evaluates a subset of attributes with respect to a set of instances.
		/// Calling this function overides any test/hold out instancs set from
		/// setHoldOutFile.
		/// </summary>
		/// <param name="subset">a bitset representing the attribute subset to be
		/// evaluated
		/// </param>
		/// <param name="holdOut">a set of instances (possibly seperate and distinct
		/// from those use to build/train the evaluator) with which to
		/// evaluate the merit of the subset
		/// </param>
		/// <returns> the "merit" of the subset on the holdOut data
		/// </returns>
		/// <exception cref="Exception">if the subset cannot be evaluated
		/// </exception>
		public override double evaluateSubset(System.Collections.BitArray subset, Instances holdOut)
		{
			int i, j;
			double errorRate;
			int numAttributes = 0;
			Instances trainCopy = null;
			Instances testCopy = null;
			
			if (m_trainingInstances.equalHeaders(holdOut) == false)
			{
				throw new System.Exception("evaluateSubset : Incompatable instance types.");
			}
			
			Remove delTransform = new Remove();
			delTransform.set_InvertSelection(true);
			// copy the training instances
			trainCopy = new Instances(m_trainingInstances);
			
			testCopy = new Instances(holdOut);
			
			// count attributes set in the BitSet
			for (i = 0; i < m_numAttribs; i++)
			{
				if (subset.Get(i))
				{
					numAttributes++;
				}
			}
			
			// set up an array of attribute indexes for the filter (+1 for the class)
			int[] featArray = new int[numAttributes + 1];
			
			for (i = 0, j = 0; i < m_numAttribs; i++)
			{
				if (subset.Get(i))
				{
					featArray[j++] = i;
				}
			}
			
			featArray[j] = m_classIndex;
			delTransform.SetAttributeIndicesArray(featArray);
			delTransform.setInputFormat(trainCopy);
			trainCopy = Filter.useFilter(trainCopy, delTransform);
			testCopy = Filter.useFilter(testCopy, delTransform);
			
			// build the classifier
			m_Classifier.buildClassifier(trainCopy);
			
			m_Evaluation = new Evaluation(trainCopy);
			m_Evaluation.evaluateModel(m_Classifier, testCopy);
			
			if (m_trainingInstances.classAttribute().Nominal)
			{
				errorRate = m_Evaluation.errorRate();
			}
			else
			{
				errorRate = m_Evaluation.meanAbsoluteError();
			}
			
			m_Evaluation = null;
			// return the negative of the error as search methods need to
			// maximize something
			return - errorRate;
		}
		
		/// <summary> Evaluates a subset of attributes with respect to a single instance.
		/// Calling this function overides any hold out/test instances set
		/// through setHoldOutFile.
		/// </summary>
		/// <param name="subset">a bitset representing the attribute subset to be
		/// evaluated
		/// </param>
		/// <param name="holdOut">a single instance (possibly not one of those used to
		/// build/train the evaluator) with which to evaluate the merit of the subset
		/// </param>
		/// <param name="retrain">true if the classifier should be retrained with respect
		/// to the new subset before testing on the holdOut instance.
		/// </param>
		/// <returns> the "merit" of the subset on the holdOut instance
		/// </returns>
		/// <exception cref="Exception">if the subset cannot be evaluated
		/// </exception>
		public override double evaluateSubset(System.Collections.BitArray subset, Instance holdOut, bool retrain)
		{
			int i, j;
			double error;
			int numAttributes = 0;
			Instances trainCopy = null;
			Instance testCopy = null;
			
			if (m_trainingInstances.equalHeaders(holdOut.dataset()) == false)
			{
				throw new System.Exception("evaluateSubset : Incompatable instance types.");
			}
			
			Remove delTransform = new Remove();
            delTransform.set_InvertSelection(true);//.setInvertSelection(true);
			// copy the training instances
			trainCopy = new Instances(m_trainingInstances);
			
			testCopy = (Instance) holdOut.copy();
			
			// count attributes set in the BitSet
			for (i = 0; i < m_numAttribs; i++)
			{
				if (subset.Get(i))
				{
					numAttributes++;
				}
			}
			
			// set up an array of attribute indexes for the filter (+1 for the class)
			int[] featArray = new int[numAttributes + 1];
			
			for (i = 0, j = 0; i < m_numAttribs; i++)
			{
				if (subset.Get(i))
				{
					featArray[j++] = i;
				}
			}
			featArray[j] = m_classIndex;
            delTransform.SetAttributeIndicesArray(featArray);//.setAttributeIndicesArray(featArray);
			delTransform.setInputFormat(trainCopy);
			
			if (retrain)
			{
				trainCopy = Filter.useFilter(trainCopy, delTransform);
				// build the classifier
				m_Classifier.buildClassifier(trainCopy);
			}
			
			delTransform.input(testCopy);
			testCopy = delTransform.output();
			
			double pred;
			double[] distrib;
			distrib = m_Classifier.distributionForInstance(testCopy);
			if (m_trainingInstances.classAttribute().Nominal)
			{
				pred = distrib[(int) testCopy.classValue()];
			}
			else
			{
				pred = distrib[0];
			}
			
			if (m_trainingInstances.classAttribute().Nominal)
			{
				error = 1.0 - pred;
			}
			else
			{
				error = testCopy.classValue() - pred;
			}
			
			// return the negative of the error as search methods need to
			// maximize something
			return - error;
		}
		
		/// <summary> Returns a string describing classifierSubsetEval
		/// 
		/// </summary>
		/// <returns> the description as a string
		/// </returns>
		public override System.String ToString()
		{
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			
			if (m_trainingInstances == null)
			{
				text.Append("\tClassifier subset evaluator has not been built yet\n");
			}
			else
			{
				text.Append("\tClassifier Subset Evaluator\n");
                text.Append("\tLearning scheme: " + Classifier.GetType().ToString() + "\n");
				text.Append("\tScheme options: ");
				System.String[] classifierOptions = new System.String[0];
				
				if (m_Classifier is OptionHandler)
				{
					classifierOptions = ((OptionHandler) m_Classifier).Options;
					
					for (int i = 0; i < classifierOptions.Length; i++)
					{
						text.Append(classifierOptions[i] + " ");
					}
				}
				
				text.Append("\n");
				text.Append("\tHold out/test set: ");
				if (!m_useTraining)
				{
					if (HoldOutFile.FullName.StartsWith("Click to set"))
					{
						text.Append("none\n");
					}
					else
					{
						text.Append(HoldOutFile.FullName + '\n');
					}
				}
				else
				{
					text.Append("Training data\n");
				}
				if (m_trainingInstances.attribute(m_classIndex).Numeric)
				{
					text.Append("\tAccuracy estimation: MAE\n");
				}
				else
				{
					text.Append("\tAccuracy estimation: classification error\n");
				}
			}
			return text.ToString();
		}
		
		/// <summary> reset to defaults</summary>
		protected internal virtual void  resetOptions()
		{
			m_trainingInstances = null;
			m_Evaluation = null;
			m_Classifier = new ZeroR();
			m_holdOutFile = new System.IO.FileInfo("Click to set hold out or test instances");
			m_holdOutInstances = null;
			m_useTraining = false;
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
				System.Console.Out.WriteLine(AttributeSelection.SelectAttributes(new ClassifierSubsetEval(), args));
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