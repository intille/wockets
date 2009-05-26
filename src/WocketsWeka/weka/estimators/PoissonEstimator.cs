/*
*    PoissonEstimator.java
*    Copyright (C) 1999 Len Trigg
*
*/
using System;
using weka.core;
namespace weka.estimators
{
	
	/// <summary> Simple probability estimator that places a single Poisson distribution
	/// over the observed values.
	/// 
	/// </summary>
	/// <author>  Len Trigg (trigg@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.4 $
	/// </version>
#if !PocketPC	
	[Serializable]
#endif
	public class PoissonEstimator : Estimator
	{
		
		/// <summary>The number of values seen </summary>
		private double m_NumValues;
		
		/// <summary>The sum of the values seen </summary>
		private double m_SumOfValues;
		
		/// <summary> The average number of times
		/// an event occurs in an interval.
		/// </summary>
		private double m_Lambda;
		
		
		/// <summary> Calculates the log factorial of a number.
		/// 
		/// </summary>
		/// <param name="x">input number.
		/// </param>
		/// <returns> log factorial of x.
		/// </returns>
		private double logFac(double x)
		{
			
			double result = 0;
			for (double i = 2; i <= x; i++)
			{
				result += System.Math.Log(i);
			}
			return result;
		}
		
		/// <summary> Returns value for Poisson distribution
		/// 
		/// </summary>
		/// <param name="x">the argument to the kernel function
		/// </param>
		/// <returns> the value for a Poisson kernel
		/// </returns>
		private double Poisson(double x)
		{
			
			return System.Math.Exp(- m_Lambda + (x * System.Math.Log(m_Lambda)) - logFac(x));
		}
		
		/// <summary> Add a new data value to the current estimator.
		/// 
		/// </summary>
		/// <param name="data">the new data value 
		/// </param>
		/// <param name="weight">the weight assigned to the data value 
		/// </param>
		public virtual void  addValue(double data, double weight)
		{
			
			m_NumValues += weight;
			m_SumOfValues += data * weight;
			if (m_NumValues != 0)
			{
				m_Lambda = m_SumOfValues / m_NumValues;
			}
		}
		
		/// <summary> Get a probability estimate for a value
		/// 
		/// </summary>
		/// <param name="data">the value to estimate the probability of
		/// </param>
		/// <returns> the estimated probability of the supplied value
		/// </returns>
		public virtual double getProbability(double data)
		{
			
			return Poisson(data);
		}
		
		/// <summary>Display a representation of this estimator </summary>
		public override System.String ToString()
		{
			
			return "Poisson Lambda = " + Utils.doubleToString(m_Lambda, 4, 2) + "\n";
		}
		
		/// <summary> Main method for testing this class.
		/// 
		/// </summary>
		/// <param name="argv">should contain a sequence of numeric values
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
		//			PoissonEstimator newEst = new PoissonEstimator();
		//			for(int i = 0; i < argv.length; i++) 
		//			{
		//				double current = Double.valueOf(argv[i]).doubleValue();
		//				System.out.println(newEst);
		//				System.out.println("Prediction for " + current 
		//					+ " = " + newEst.getProbability(current));
		//				newEst.addValue(current, 1);
		//			}
		//
		//		} 
		//		catch (Exception e) 
		//		{
		//			System.out.println(e.getMessage());
		//		}
		//	}
	}
}