/*
*    DKConditionalEstimator.java
*    Copyright (C) 1999 Len Trigg
*
*/
using System;
using weka.core;
namespace weka.estimators
{
	
	/// <summary> Conditional probability estimator for a discrete domain conditional upon
	/// a numeric domain.
	/// 
	/// </summary>
	/// <author>  Len Trigg (trigg@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.4 $
	/// </version>
	public class DKConditionalEstimator : ConditionalEstimator
	{
		
		/// <summary>Hold the sub-estimators </summary>
		private KernelEstimator[] m_Estimators;
		
		/// <summary>Hold the weights for each of the sub-estimators </summary>
		private DiscreteEstimator m_Weights;
		
		/// <summary> Constructor
		/// 
		/// </summary>
		/// <param name="numSymbols">the number of symbols 
		/// </param>
		/// <param name="precision">the  precision to which numeric values are given. For
		/// example, if the precision is stated to be 0.1, the values in the
		/// interval (0.25,0.35] are all treated as 0.3. 
		/// </param>
		public DKConditionalEstimator(int numSymbols, double precision)
		{
			
			m_Estimators = new KernelEstimator[numSymbols];
			for (int i = 0; i < numSymbols; i++)
			{
				m_Estimators[i] = new KernelEstimator(precision);
			}
			m_Weights = new DiscreteEstimator(numSymbols, true);
		}
		
		/// <summary> Add a new data value to the current estimator.
		/// 
		/// </summary>
		/// <param name="data">the new data value 
		/// </param>
		/// <param name="given">the new value that data is conditional upon 
		/// </param>
		/// <param name="weight">the weight assigned to the data value 
		/// </param>
		public virtual void  addValue(double data, double given, double weight)
		{
			
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			m_Estimators[(int) data].addValue(given, weight);
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			m_Weights.addValue((int) data, weight);
		}
		
		/// <summary> Get a probability estimator for a value
		/// 
		/// </summary>
		/// <param name="data">the value to estimate the probability of
		/// </param>
		/// <param name="given">the new value that data is conditional upon 
		/// </param>
		/// <returns> the estimator for the supplied value given the condition
		/// </returns>
		public virtual Estimator getEstimator(double given)
		{
			
			Estimator result = new DiscreteEstimator(m_Estimators.Length, false);
			for (int i = 0; i < m_Estimators.Length; i++)
			{
				//System.out.println("Val " + i
				//			 + " Weight:" + m_Weights.getProbability(i)
				//			 +" EstProb(" + given + ")="
				//			 + m_Estimators[i].getProbability(given));
				result.addValue(i, m_Weights.getProbability(i) * m_Estimators[i].getProbability(given));
			}
			return result;
		}
		
		/// <summary> Get a probability estimate for a value
		/// 
		/// </summary>
		/// <param name="data">the value to estimate the probability of
		/// </param>
		/// <param name="given">the new value that data is conditional upon 
		/// </param>
		/// <returns> the estimated probability of the supplied value
		/// </returns>
		public virtual double getProbability(double data, double given)
		{
			
			return getEstimator(given).getProbability(data);
		}
		
		/// <summary> Display a representation of this estimator</summary>
		public override System.String ToString()
		{
			
			System.String result = "DK Conditional Estimator. " + m_Estimators.Length + " sub-estimators:\n";
			for (int i = 0; i < m_Estimators.Length; i++)
			{
				result += ("Sub-estimator " + i + ": " + m_Estimators[i]);
			}
			result += ("Weights of each estimator given by " + m_Weights);
			return result;
		}
		
		
		/// <summary> Main method for testing this class.
		/// 
		/// </summary>
		/// <param name="argv">should contain a sequence of pairs of integers which
		/// will be treated as pairs of symbolic, numeric.
		/// </param>
		//	public static void main(String [] argv) 
		//	{
		//    
		//		try 
		//		{
		//			if (argv.length == 0) 
		//			{
		//				System.out.println("Please specify a set of instances.");
		//				return;
		//			}
		//			int currentA = Integer.parseInt(argv[0]);
		//			int maxA = currentA;
		//			int currentB = Integer.parseInt(argv[1]);
		//			int maxB = currentB;
		//			for(int i = 2; i < argv.length - 1; i += 2) 
		//			{
		//				currentA = Integer.parseInt(argv[i]);
		//				currentB = Integer.parseInt(argv[i + 1]);
		//				if (currentA > maxA) 
		//				{
		//					maxA = currentA;
		//				}
		//				if (currentB > maxB) 
		//				{
		//					maxB = currentB;
		//				}
		//			}
		//			DKConditionalEstimator newEst = new DKConditionalEstimator(maxA + 1,
		//				1);
		//			for(int i = 0; i < argv.length - 1; i += 2) 
		//			{
		//				currentA = Integer.parseInt(argv[i]);
		//				currentB = Integer.parseInt(argv[i + 1]);
		//				System.out.println(newEst);
		//				System.out.println("Prediction for " + currentA + '|' + currentB 
		//					+ " = "
		//					+ newEst.getProbability(currentA, currentB));
		//				newEst.addValue(currentA, currentB, 1);
		//			}
		//		} 
		//		catch (Exception e) 
		//		{
		//			System.out.println(e.getMessage());
		//		}
		//	}
	}
}