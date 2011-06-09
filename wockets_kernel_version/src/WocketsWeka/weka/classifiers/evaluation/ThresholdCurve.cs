/*
*    ThresholdCurve.java
*    Copyright (C) 2002 University of Waikato
*
*/
using System;
//UPGRADE_TODO: The type 'weka.classifiers.functions.VotedPerceptron' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using VotedPerceptron = weka.classifiers.functions.VotedPerceptron;
using Utils = weka.core.Utils;
using Attribute = weka.core.Attribute;
using FastVector = weka.core.FastVector;
using Instance = weka.core.Instance;
using Instances = weka.core.Instances;
using Classifier = weka.classifiers.Classifier;
namespace weka.classifiers.evaluation
{
	
	/// <summary> Generates points illustrating prediction tradeoffs that can be obtained
	/// by varying the threshold value between classes. For example, the typical 
	/// threshold value of 0.5 means the predicted probability of "positive" must be
	/// higher than 0.5 for the instance to be predicted as "positive". The 
	/// resulting dataset can be used to visualize precision/recall tradeoff, or 
	/// for ROC curve analysis (true positive rate vs false positive rate).
	/// 
	/// </summary>
	/// <author>  Len Trigg (len@reeltwo.com)
	/// </author>
	/// <version>  $Revision: 1.18 $
	/// </version>
	public class ThresholdCurve
	{
		
		/// <summary>The name of the relation used in threshold curve datasets </summary>
		public const System.String RELATION_NAME = "ThresholdCurve";
		
		public const System.String TRUE_POS_NAME = "True Positives";
		public const System.String FALSE_NEG_NAME = "False Negatives";
		public const System.String FALSE_POS_NAME = "False Positives";
		public const System.String TRUE_NEG_NAME = "True Negatives";
		public const System.String FP_RATE_NAME = "False Positive Rate";
		public const System.String TP_RATE_NAME = "True Positive Rate";
		public const System.String PRECISION_NAME = "Precision";
		public const System.String RECALL_NAME = "Recall";
		public const System.String FALLOUT_NAME = "Fallout";
		public const System.String FMEASURE_NAME = "FMeasure";
		public const System.String THRESHOLD_NAME = "Threshold";
		
		/// <summary> Calculates the performance stats for the default class and return 
		/// results as a set of Instances. The
		/// structure of these Instances is as follows:<p> <ul> 
		/// <li> <b>True Positives </b>
		/// <li> <b>False Negatives</b>
		/// <li> <b>False Positives</b>
		/// <li> <b>True Negatives</b>
		/// <li> <b>False Positive Rate</b>
		/// <li> <b>True Positive Rate</b>
		/// <li> <b>Precision</b>
		/// <li> <b>Recall</b>  
		/// <li> <b>Fallout</b>  
		/// <li> <b>Threshold</b> contains the probability threshold that gives
		/// rise to the previous performance values. 
		/// </ul> <p>
		/// For the definitions of these measures, see TwoClassStats <p>
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
			
			double totPos = 0, totNeg = 0;
			double[] probs = getProbabilities(predictions, classIndex);
			
			// Get distribution of positive/negatives
			for (int i = 0; i < probs.Length; i++)
			{
				NominalPrediction pred = (NominalPrediction) predictions.elementAt(i);
				if (pred.actual() == weka.classifiers.evaluation.Prediction_Fields.MISSING_VALUE)
				{
					System.Console.Error.WriteLine(GetType().FullName + " Skipping prediction with missing class value");
					continue;
				}
				if (pred.weight() < 0)
				{
					System.Console.Error.WriteLine(GetType().FullName + " Skipping prediction with negative weight");
					continue;
				}
				if (pred.actual() == classIndex)
				{
					totPos += pred.weight();
				}
				else
				{
					totNeg += pred.weight();
				}
			}
			
			Instances insts = makeHeader();
			int[] sorted = Utils.sort(probs);
			TwoClassStats tc = new TwoClassStats(totPos, totNeg, 0, 0);
			double threshold = 0;
			double cumulativePos = 0;
			double cumulativeNeg = 0;
			for (int i = 0; i < sorted.Length; i++)
			{
				
				if ((i == 0) || (probs[sorted[i]] > threshold))
				{
					tc.TruePositive = tc.TruePositive - cumulativePos;
					tc.FalseNegative = tc.FalseNegative + cumulativePos;
					tc.FalsePositive = tc.FalsePositive - cumulativeNeg;
					tc.TrueNegative = tc.TrueNegative + cumulativeNeg;
					threshold = probs[sorted[i]];
					insts.add(makeInstance(tc, threshold));
					cumulativePos = 0;
					cumulativeNeg = 0;
					if (i == sorted.Length - 1)
					{
						break;
					}
				}
				
				NominalPrediction pred = (NominalPrediction) predictions.elementAt(sorted[i]);
				
				if (pred.actual() == weka.classifiers.evaluation.Prediction_Fields.MISSING_VALUE)
				{
					System.Console.Error.WriteLine(GetType().FullName + " Skipping prediction with missing class value");
					continue;
				}
				if (pred.weight() < 0)
				{
					System.Console.Error.WriteLine(GetType().FullName + " Skipping prediction with negative weight");
					continue;
				}
				if (pred.actual() == classIndex)
				{
					cumulativePos += pred.weight();
				}
				else
				{
					cumulativeNeg += pred.weight();
				}
				
				/*
				System.out.println(tc + " " + probs[sorted[i]] 
				+ " " + (pred.actual() == classIndex));
				*/
				/*if ((i != (sorted.length - 1)) &&
				((i == 0) ||  
				(probs[sorted[i]] != probs[sorted[i - 1]]))) {
				insts.add(makeInstance(tc, probs[sorted[i]]));
				}*/
			}
			return insts;
		}
		
		/// <summary> Calculates the n point precision result, which is the precision averaged
		/// over n evenly spaced (w.r.t recall) samples of the curve.
		/// 
		/// </summary>
		/// <param name="tcurve">a previously extracted threshold curve Instances.
		/// </param>
		/// <param name="n">the number of points to average over.
		/// </param>
		/// <returns> the n-point precision.
		/// </returns>
		public static double getNPointPrecision(Instances tcurve, int n)
		{
			
			if (!RELATION_NAME.Equals(tcurve.relationName()) || (tcurve.numInstances() == 0))
			{
				return System.Double.NaN;
			}
			int recallInd = tcurve.attribute(RECALL_NAME).index();
			int precisInd = tcurve.attribute(PRECISION_NAME).index();
			double[] recallVals = tcurve.attributeToDoubleArray(recallInd);
			int[] sorted = Utils.sort(recallVals);
			double isize = 1.0 / (n - 1);
			double psum = 0;
			for (int i = 0; i < n; i++)
			{
				int pos = binarySearch(sorted, recallVals, i * isize);
				double recall = recallVals[sorted[pos]];
				double precis = tcurve.instance(sorted[pos]).value_Renamed(precisInd);
				/*
				System.err.println("Point " + (i + 1) + ": i=" + pos 
				+ " r=" + (i * isize)
				+ " p'=" + precis 
				+ " r'=" + recall);
				*/
				// interpolate figures for non-endpoints
				while ((pos != 0) && (pos < sorted.Length - 1))
				{
					pos++;
					double recall2 = recallVals[sorted[pos]];
					if (recall2 != recall)
					{
						double precis2 = tcurve.instance(sorted[pos]).value_Renamed(precisInd);
						double slope = (precis2 - precis) / (recall2 - recall);
						double offset = precis - recall * slope;
						precis = isize * i * slope + offset;
						/*
						System.err.println("Point2 " + (i + 1) + ": i=" + pos 
						+ " r=" + (i * isize)
						+ " p'=" + precis2 
						+ " r'=" + recall2
						+ " p''=" + precis);
						*/
						break;
					}
				}
				psum += precis;
			}
			return psum / n;
		}
		
		/// <summary> Calculates the area under the ROC curve.  This is normalised so
		/// that 0.5 is random, 1.0 is perfect and 0.0 is bizarre.
		/// 
		/// </summary>
		/// <param name="tcurve">a previously extracted threshold curve Instances.
		/// </param>
		/// <returns> the ROC area, or Double.NaN if you don't pass in 
		/// a ThresholdCurve generated Instances. 
		/// </returns>
		public static double getROCArea(Instances tcurve)
		{
			
			//UPGRADE_NOTE: Final was removed from the declaration of 'n '. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1003'"
			int n = tcurve.numInstances();
			if (!RELATION_NAME.Equals(tcurve.relationName()) || (n == 0))
			{
				return System.Double.NaN;
			}
			//UPGRADE_NOTE: Final was removed from the declaration of 'tpInd '. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1003'"
			int tpInd = tcurve.attribute(TRUE_POS_NAME).index();
			//UPGRADE_NOTE: Final was removed from the declaration of 'fpInd '. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1003'"
			int fpInd = tcurve.attribute(FALSE_POS_NAME).index();
			//UPGRADE_NOTE: Final was removed from the declaration of 'tpVals '. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1003'"
			double[] tpVals = tcurve.attributeToDoubleArray(tpInd);
			//UPGRADE_NOTE: Final was removed from the declaration of 'fpVals '. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1003'"
			double[] fpVals = tcurve.attributeToDoubleArray(fpInd);
			//UPGRADE_NOTE: Final was removed from the declaration of 'tp0 '. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1003'"
			double tp0 = tpVals[0];
			//UPGRADE_NOTE: Final was removed from the declaration of 'fp0 '. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1003'"
			double fp0 = fpVals[0];
			double area = 0.0;
			//starts at high values and goes down
			double xlast = 1.0;
			double ylast = 1.0;
			for (int i = 1; i < n; i++)
			{
				//UPGRADE_NOTE: Final was removed from the declaration of 'x '. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1003'"
				double x = fpVals[i] / fp0;
				//UPGRADE_NOTE: Final was removed from the declaration of 'y '. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1003'"
				double y = tpVals[i] / tp0;
				//UPGRADE_NOTE: Final was removed from the declaration of 'areaDelta '. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1003'"
				double areaDelta = (y + ylast) * (xlast - x) / 2.0;
				/*
				System.err.println("[" + i + "]"
				+ " x=" + x
				+ " y'=" + y
				+ " xl=" + xlast
				+ " yl=" + ylast
				+ " a'=" + areaDelta);
				*/
				
				area += areaDelta;
				xlast = x;
				ylast = y;
			}
			
			//make sure ends at 0,0
			if (xlast > 0.0)
			{
				//UPGRADE_NOTE: Final was removed from the declaration of 'areaDelta '. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1003'"
				double areaDelta = ylast * xlast / 2.0;
				//System.err.println(" a'=" + areaDelta);
				area += areaDelta;
			}
			//System.err.println(" area'=" + area);
			return area;
		}
		
		/// <summary> Gets the index of the instance with the closest threshold value to the
		/// desired target
		/// 
		/// </summary>
		/// <param name="tcurve">a set of instances that have been generated by this class
		/// </param>
		/// <param name="threshold">the target threshold
		/// </param>
		/// <returns> the index of the instance that has threshold closest to
		/// the target, or -1 if this could not be found (i.e. no data, or
		/// bad threshold target)
		/// </returns>
		public static int getThresholdInstance(Instances tcurve, double threshold)
		{
			
			if (!RELATION_NAME.Equals(tcurve.relationName()) || (tcurve.numInstances() == 0) || (threshold < 0) || (threshold > 1.0))
			{
				return - 1;
			}
			if (tcurve.numInstances() == 1)
			{
				return 0;
			}
			double[] tvals = tcurve.attributeToDoubleArray(tcurve.numAttributes() - 1);
			int[] sorted = Utils.sort(tvals);
			return binarySearch(sorted, tvals, threshold);
		}
		
		
		private static int binarySearch(int[] index, double[] vals, double target)
		{
			
			int lo = 0, hi = index.Length - 1;
			while (hi - lo > 1)
			{
				int mid = lo + (hi - lo) / 2;
				double midval = vals[index[mid]];
				if (target > midval)
				{
					lo = mid;
				}
				else if (target < midval)
				{
					hi = mid;
				}
				else
				{
					while ((mid > 0) && (vals[index[mid - 1]] == target))
					{
						mid--;
					}
					return mid;
				}
			}
			return lo;
		}
		
		
		private double[] getProbabilities(FastVector predictions, int classIndex)
		{
			
			// sort by predicted probability of the desired class.
			double[] probs = new double[predictions.size()];
			for (int i = 0; i < probs.Length; i++)
			{
				NominalPrediction pred = (NominalPrediction) predictions.elementAt(i);
				probs[i] = pred.distribution()[classIndex];
			}
			return probs;
		}
		
		private Instances makeHeader()
		{
			
			FastVector fv = new FastVector();
			fv.addElement(new Attribute(TRUE_POS_NAME));
			fv.addElement(new Attribute(FALSE_NEG_NAME));
			fv.addElement(new Attribute(FALSE_POS_NAME));
			fv.addElement(new Attribute(TRUE_NEG_NAME));
			fv.addElement(new Attribute(FP_RATE_NAME));
			fv.addElement(new Attribute(TP_RATE_NAME));
			fv.addElement(new Attribute(PRECISION_NAME));
			fv.addElement(new Attribute(RECALL_NAME));
			fv.addElement(new Attribute(FALLOUT_NAME));
			fv.addElement(new Attribute(FMEASURE_NAME));
			fv.addElement(new Attribute(THRESHOLD_NAME));
			return new Instances(RELATION_NAME, fv, 100);
		}
		
		private Instance makeInstance(TwoClassStats tc, double prob)
		{
			
			int count = 0;
			double[] vals = new double[11];
			vals[count++] = tc.TruePositive;
			vals[count++] = tc.FalseNegative;
			vals[count++] = tc.FalsePositive;
			vals[count++] = tc.TrueNegative;
			vals[count++] = tc.FalsePositiveRate;
			vals[count++] = tc.TruePositiveRate;
			vals[count++] = tc.Precision;
			vals[count++] = tc.Recall;
			vals[count++] = tc.Fallout;
			vals[count++] = tc.FMeasure;
			vals[count++] = prob;
			return new Instance(1.0, vals);
		}
		
		//	/**
		//	 * Tests the ThresholdCurve generation from the command line.
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
		//			if (false) 
		//			{
		//				System.out.println(ThresholdCurve.getNPointPrecision(inst, 11));
		//			} 
		//			else 
		//			{
		//				inst.setClassIndex(inst.numAttributes() - 1);
		//				ThresholdCurve tc = new ThresholdCurve();
		//				EvaluationUtils eu = new EvaluationUtils();
		//				Classifier classifier = new weka.classifiers.functions.Logistic();
		//				FastVector predictions = new FastVector();
		//				for (int i = 0; i < 2; i++) 
		//				{ // Do two runs.
		//					eu.setSeed(i);
		//					predictions.appendXmlElements(eu.getCVPredictions(classifier, inst, 10));
		//					//System.out.println("\n\n\n");
		//				}
		//				Instances result = tc.getCurve(predictions);
		//				System.out.println(result);
		//			}
		//		} 
		//		catch (Exception ex) 
		//		{
		//			ex.printStackTrace();
		//		}
		//	}
	}
}