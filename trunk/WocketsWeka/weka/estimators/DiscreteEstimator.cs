/*
*    DiscreteEstimator.java
*    Copyright (C) 1999 Len Trigg
*
*/
using System;
using Utils = weka.core.Utils;
namespace weka.estimators
{
	
	
	/// <summary> Simple symbolic probability estimator based on symbol counts.
	/// 
	/// </summary>
	/// <author>  Len Trigg (trigg@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.6 $
	/// </version>
#if !PocketPC
    [Serializable]
#endif
	public class DiscreteEstimator : Estimator
	{
		/// <summary> Gets the number of symbols this estimator operates with
		/// 
		/// </summary>
		/// <returns> the number of estimator symbols
		/// </returns>
		virtual public int NumSymbols
		{
			get
			{
				
				return (m_Counts == null)?0:m_Counts.Length;
			}
			
		}
		/// <summary> Get the sum of all the counts
		/// 
		/// </summary>
		/// <returns> the total sum of counts
		/// </returns>
		virtual public double SumOfCounts
		{
			get
			{
				
				return m_SumOfCounts;
			}
			
		}
		
		/// <summary>Hold the counts </summary>
		private double[] m_Counts;
		
		/// <summary>Hold the sum of counts </summary>
		private double m_SumOfCounts;
		
		
		/// <summary> Constructor
		/// 
		/// </summary>
		/// <param name="numSymbols">the number of possible symbols (remember to include 0)
		/// </param>
		/// <param name="laplace">if true, counts will be initialised to 1
		/// </param>
		public DiscreteEstimator(int numSymbols, bool laplace)
		{
			
			m_Counts = new double[numSymbols];
			m_SumOfCounts = 0;
			if (laplace)
			{
				for (int i = 0; i < numSymbols; i++)
				{
					m_Counts[i] = 1;
				}
				m_SumOfCounts = (double) numSymbols;
			}
		}
		
		/// <summary> Constructor
		/// 
		/// </summary>
		/// <param name="nSymbols">the number of possible symbols (remember to include 0)
		/// </param>
		/// <param name="fPrior">value with which counts will be initialised
		/// </param>
		public DiscreteEstimator(int nSymbols, double fPrior)
		{
			
			m_Counts = new double[nSymbols];
			for (int iSymbol = 0; iSymbol < nSymbols; iSymbol++)
			{
				m_Counts[iSymbol] = fPrior;
			}
			m_SumOfCounts = fPrior * (double) nSymbols;
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
			
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			m_Counts[(int) data] += weight;
			m_SumOfCounts += weight;
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
			
			if (m_SumOfCounts == 0)
			{
				return 0;
			}
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			return (double) m_Counts[(int) data] / m_SumOfCounts;
		}
		
		
		/// <summary> Get the count for a value
		/// 
		/// </summary>
		/// <param name="data">the value to get the count of
		/// </param>
		/// <returns> the count of the supplied value
		/// </returns>
		public virtual double getCount(double data)
		{
			
			if (m_SumOfCounts == 0)
			{
				return 0;
			}
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			return m_Counts[(int) data];
		}
		
		
		/// <summary> Display a representation of this estimator</summary>
		public override System.String ToString()
		{
			
			System.String result = "Discrete Estimator. Counts = ";
			if (m_SumOfCounts > 1)
			{
				for (int i = 0; i < m_Counts.Length; i++)
				{
					result += (" " + Utils.doubleToString(m_Counts[i], 2));
				}
				result += ("  (Total = " + Utils.doubleToString(m_SumOfCounts, 2) + ")\n");
			}
			else
			{
				for (int i = 0; i < m_Counts.Length; i++)
				{
					result += (" " + m_Counts[i]);
				}
				result += ("  (Total = " + m_SumOfCounts + ")\n");
			}
			return result;
		}
		
		/// <summary> Main method for testing this class.
		/// 
		/// </summary>
		/// <param name="argv">should contain a sequence of integers which
		/// will be treated as symbolic.
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
		//			int current = Integer.parseInt(argv[0]);
		//			int max = current;
		//			for(int i = 1; i < argv.length; i++) 
		//			{
		//				current = Integer.parseInt(argv[i]);
		//				if (current > max) 
		//				{
		//					max = current;
		//				}
		//			}
		//			DiscreteEstimator newEst = new DiscreteEstimator(max + 1, true);
		//			for(int i = 0; i < argv.length; i++) 
		//			{
		//				current = Integer.parseInt(argv[i]);
		//				System.out.println(newEst);
		//				System.out.println("Prediction for " + current 
		//					+ " = " + newEst.getProbability(current));
		//				newEst.addValue(current, 1);
		//			}
		//		} 
		//		catch (Exception e) 
		//		{
		//			System.out.println(e.getMessage());
		//		}
		//	}
	}
}