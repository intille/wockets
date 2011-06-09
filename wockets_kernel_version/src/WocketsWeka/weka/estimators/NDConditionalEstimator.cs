/*
*    NDConditionalEstimator.java
*    Copyright (C) 1999 Len Trigg
*
*/
using System;
using weka.core;
namespace weka.estimators
{
	
	/// <summary> Conditional probability estimator for a numeric domain conditional upon
	/// a discrete domain (utilises separate normal estimators for each discrete
	/// conditioning value).
	/// 
	/// </summary>
	/// <author>  Len Trigg (trigg@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.4 $
	/// </version>
	public class NDConditionalEstimator : ConditionalEstimator
	{
		
		/// <summary>Hold the sub-estimators </summary>
		private NormalEstimator[] m_Estimators;
		
		/// <summary> Constructor
		/// 
		/// </summary>
		/// <param name="numCondSymbols">the number of conditioning symbols 
		/// </param>
		/// <param name="precision">the  precision to which numeric values are given. For
		/// example, if the precision is stated to be 0.1, the values in the
		/// interval (0.25,0.35] are all treated as 0.3. 
		/// </param>
		public NDConditionalEstimator(int numCondSymbols, double precision)
		{
			
			m_Estimators = new NormalEstimator[numCondSymbols];
			for (int i = 0; i < numCondSymbols; i++)
			{
				m_Estimators[i] = new NormalEstimator(precision);
			}
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
			m_Estimators[(int) given].addValue(data, weight);
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
			
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			return m_Estimators[(int) given];
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
			
			System.String result = "ND Conditional Estimator. " + m_Estimators.Length + " sub-estimators:\n";
			for (int i = 0; i < m_Estimators.Length; i++)
			{
				result += ("Sub-estimator " + i + ": " + m_Estimators[i]);
			}
			return result;
		}
		
		/// <summary> Main method for testing this class.
		/// 
		/// </summary>
		/// <param name="argv">should contain a sequence of pairs of integers which
		/// will be treated as numeric, symbolic.
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
		//			NDConditionalEstimator newEst = new NDConditionalEstimator(maxB + 1,
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