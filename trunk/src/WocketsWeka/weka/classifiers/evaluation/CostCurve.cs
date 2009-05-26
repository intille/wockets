/*
*    CostCurve.java
*    Copyright (C) 2001 Mark Hall
*
*/
using System;
//UPGRADE_TODO: The type 'weka.classifiers.functions.Logistic' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using Logistic = weka.classifiers.functions.Logistic;
using Utils = weka.core.Utils;
using Attribute = weka.core.Attribute;
using FastVector = weka.core.FastVector;
using Instance = weka.core.Instance;
using Instances = weka.core.Instances;
using Classifier = weka.classifiers.Classifier;
namespace weka.classifiers.evaluation
{
	
	/// <summary> Generates points illustrating probablity cost tradeoffs that can be 
	/// obtained by varying the threshold value between classes. For example, 
	/// the typical threshold value of 0.5 means the predicted probability of 
	/// "positive" must be higher than 0.5 for the instance to be predicted as 
	/// "positive".
	/// 
	/// </summary>
	/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.6 $
	/// </version>
	
	public class CostCurve
	{
		
		/// <summary>The name of the relation used in cost curve datasets </summary>
		public const System.String RELATION_NAME = "CostCurve";
		
		public const System.String PROB_COST_FUNC_NAME = "Probability Cost Function";
		public const System.String NORM_EXPECTED_COST_NAME = "Normalized Expected Cost";
		public const System.String THRESHOLD_NAME = "Threshold";
		
		/// <summary> Calculates the performance stats for the default class and return 
		/// results as a set of Instances. The
		/// structure of these Instances is as follows:<p> <ul> 
		/// <li> <b>Probability Cost Function </b>
		/// <li> <b>Normalized Expected Cost</b>
		/// <li> <b>Threshold</b> contains the probability threshold that gives
		/// rise to the previous performance values. 
		/// </ul> <p>
		/// 
		/// </summary>
		/// <seealso cref="TwoClassStats">
		/// </seealso>
		/// <param name="classIndex">index of the class of interest.
		/// </param>
		/// <returns> datapoints as a set of instances, null if no predictions
		/// have been made.
		/// </returns>
		public virtual Instances getCurve(FastVector predictions)
		{
			
			if (predictions.size() == 0)
			{
				return null;
			}
			return getCurve(predictions, ((NominalPrediction) predictions.elementAt(0)).distribution().Length - 1);
		}
		
		/// <summary> Calculates the performance stats for the desired class and return 
		/// results as a set of Instances.
		/// 
		/// </summary>
		/// <param name="classIndex">index of the class of interest.
		/// </param>
		/// <returns> datapoints as a set of instances.
		/// </returns>
		public virtual Instances getCurve(FastVector predictions, int classIndex)
		{
			
			if ((predictions.size() == 0) || (((NominalPrediction) predictions.elementAt(0)).distribution().Length <= classIndex))
			{
				return null;
			}
			
			ThresholdCurve tc = new ThresholdCurve();
			Instances threshInst = tc.getCurve(predictions, classIndex);
			
			Instances insts = makeHeader();
			int fpind = threshInst.attribute(ThresholdCurve.FP_RATE_NAME).index();
			int tpind = threshInst.attribute(ThresholdCurve.TP_RATE_NAME).index();
			int threshind = threshInst.attribute(ThresholdCurve.THRESHOLD_NAME).index();
			
			double[] vals;
			double fpval, tpval, thresh;
			for (int i = 0; i < threshInst.numInstances(); i++)
			{
				fpval = threshInst.instance(i).value_Renamed(fpind);
				tpval = threshInst.instance(i).value_Renamed(tpind);
				thresh = threshInst.instance(i).value_Renamed(threshind);
				vals = new double[3];
				vals[0] = 0; vals[1] = fpval; vals[2] = thresh;
				insts.add(new Instance(1.0, vals));
				vals = new double[3];
				vals[0] = 1; vals[1] = 1.0 - tpval; vals[2] = thresh;
				insts.add(new Instance(1.0, vals));
			}
			
			return insts;
		}
		
		private Instances makeHeader()
		{
			
			FastVector fv = new FastVector();
			fv.addElement(new Attribute(PROB_COST_FUNC_NAME));
			fv.addElement(new Attribute(NORM_EXPECTED_COST_NAME));
			fv.addElement(new Attribute(THRESHOLD_NAME));
			return new Instances(RELATION_NAME, fv, 100);
		}
		
		//	/**
		//	 * Tests the CostCurve generation from the command line.
		//	 * The classifier is currently hardcoded. Pipe in an arff file.
		//	 *
		//	 * @param args currently ignored
		//	 */
		//	public static void main(String [] args) 
		//	{
		//
		//		try 
		//		{
		//      
		//			Instances inst = new Instances(new java.io.InputStreamReader(System.in));
		//      
		//			inst.setClassIndex(inst.numAttributes() - 1);
		//			CostCurve cc = new CostCurve();
		//			EvaluationUtils eu = new EvaluationUtils();
		//			Classifier classifier = new weka.classifiers.functions.Logistic();
		//			FastVector predictions = new FastVector();
		//			for (int i = 0; i < 2; i++) 
		//			{ // Do two runs.
		//				eu.setSeed(i);
		//				predictions.appendXmlElements(eu.getCVPredictions(classifier, inst, 10));
		//				//System.out.println("\n\n\n");
		//			}
		//			Instances result = cc.getCurve(predictions);
		//			System.out.println(result);
		//      
		//		} 
		//		catch (Exception ex) 
		//		{
		//			ex.printStackTrace();
		//		}
		//	}
	}
}