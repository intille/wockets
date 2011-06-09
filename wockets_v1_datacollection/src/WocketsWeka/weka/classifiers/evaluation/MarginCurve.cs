/*
*    MarginCurve.java
*    Copyright (C) 2002 University of Waikato
*
*/
using System;
//UPGRADE_TODO: The type 'weka.classifiers.meta.LogitBoost' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using LogitBoost = weka.classifiers.meta.LogitBoost;
using Utils = weka.core.Utils;
using Attribute = weka.core.Attribute;
using FastVector = weka.core.FastVector;
using Instance = weka.core.Instance;
using Instances = weka.core.Instances;
namespace weka.classifiers.evaluation
{
	
	/// <summary> Generates points illustrating the prediction margin. The margin is defined
	/// as the difference between the probability predicted for the actual class and
	/// the highest probability predicted for the other classes. One hypothesis
	/// as to the good performance of boosting algorithms is that they increaes the
	/// margins on the training data and this gives better performance on test data.
	/// 
	/// </summary>
	/// <author>  Len Trigg (len@reeltwo.com)
	/// </author>
	/// <version>  $Revision: 1.9 $
	/// </version>
	public class MarginCurve
	{
		
		/// <summary> Calculates the cumulative margin distribution for the set of
		/// predictions, returning the result as a set of Instances. The
		/// structure of these Instances is as follows:<p> <ul> 
		/// <li> <b>Margin</b> contains the margin value (which should be plotted
		/// as an x-coordinate) 
		/// <li> <b>Current</b> contains the count of instances with the current 
		/// margin (plot as y axis)
		/// <li> <b>Cumulative</b> contains the count of instances with margin
		/// less than or equal to the current margin (plot as y axis)
		/// </ul> <p>
		/// 
		/// </summary>
		/// <returns> datapoints as a set of instances, null if no predictions
		/// have been made.  
		/// </returns>
		public virtual Instances getCurve(FastVector predictions)
		{
			
			if (predictions.size() == 0)
			{
				return null;
			}
			
			Instances insts = makeHeader();
			double[] margins = getMargins(predictions);
			int[] sorted = Utils.sort(margins);
			int binMargin = 0;
			int totalMargin = 0;
			insts.add(makeInstance(- 1, binMargin, totalMargin));
			for (int i = 0; i < sorted.Length; i++)
			{
				double current = margins[sorted[i]];
				double weight = ((NominalPrediction) predictions.elementAt(sorted[i])).weight();
				totalMargin = (int) (totalMargin + weight);
				binMargin = (int) (binMargin + weight);
				if (true)
				{
					insts.add(makeInstance(current, binMargin, totalMargin));
					binMargin = 0;
				}
			}
			return insts;
		}
		
		/// <summary> Pulls all the margin values out of a vector of NominalPredictions.
		/// 
		/// </summary>
		/// <param name="predictions">a FastVector containing NominalPredictions
		/// </param>
		/// <returns> an array of margin values.
		/// </returns>
		private double[] getMargins(FastVector predictions)
		{
			
			// sort by predicted probability of the desired class.
			double[] margins = new double[predictions.size()];
			for (int i = 0; i < margins.Length; i++)
			{
				NominalPrediction pred = (NominalPrediction) predictions.elementAt(i);
				margins[i] = pred.margin();
			}
			return margins;
		}
		
		/// <summary> Creates an Instances object with the attributes we will be calculating.
		/// 
		/// </summary>
		/// <returns> the Instances structure.
		/// </returns>
		private Instances makeHeader()
		{
			
			FastVector fv = new FastVector();
			fv.addElement(new Attribute("Margin"));
			fv.addElement(new Attribute("Current"));
			fv.addElement(new Attribute("Cumulative"));
			return new Instances("MarginCurve", fv, 100);
		}
		
		/// <summary> Creates an Instance object with the attributes calculated.
		/// 
		/// </summary>
		/// <param name="margin">the margin for this data point.
		/// </param>
		/// <param name="current">the number of instances with this margin.
		/// </param>
		/// <param name="cumulative">the number of instances with margin less than or equal
		/// to this margin.
		/// </param>
		/// <returns> the Instance object.
		/// </returns>
		private Instance makeInstance(double margin, int current, int cumulative)
		{
			
			int count = 0;
			double[] vals = new double[3];
			vals[count++] = margin;
			vals[count++] = current;
			vals[count++] = cumulative;
			return new Instance(1.0, vals);
		}
		
		//	/**
		//	 * Tests the MarginCurve generation from the command line.
		//	 * The classifier is currently hardcoded. Pipe in an arff file.
		//	 *
		//	 * @param args currently ignored
		//	 */
		//	public static void main(String [] args) 
		//	{
		//
		//		try 
		//		{
		//			Utils.SMALL = 0;
		//			Instances inst = new Instances(new java.io.InputStreamReader(System.in));
		//			inst.setClassIndex(inst.numAttributes() - 1);
		//			MarginCurve tc = new MarginCurve();
		//			EvaluationUtils eu = new EvaluationUtils();
		//			weka.classifiers.meta.LogitBoost classifier 
		//				= new weka.classifiers.meta.LogitBoost();
		//			classifier.setNumIterations(20);
		//			FastVector predictions 
		//				= eu.getTrainTestPredictions(classifier, inst, inst);
		//			Instances result = tc.getCurve(predictions);
		//			System.out.println(result);
		//		} 
		//		catch (Exception ex) 
		//		{
		//			ex.printStackTrace();
		//		}
		//	}
	}
}