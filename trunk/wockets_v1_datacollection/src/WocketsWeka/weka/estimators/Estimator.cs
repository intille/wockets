/*
*    Estimator.java
*    Copyright (C) 1999 Len Trigg
*
*/
using System;
namespace weka.estimators
{
	
	/// <summary> Interface for probability estimators. Example code: <p>
	/// 
	/// <code> <pre>
	/// // Create a discrete estimator that takes values 0 to 9
	/// DiscreteEstimator newEst = new DiscreteEstimator(10, true);
	/// 
	/// // Create 50 random integers first predicting the probability of the
	/// // value, then adding the value to the estimator
	/// Random r = new Random(seed);
	/// for(int i = 0; i < 50; i++) {
	/// current = Math.abs(r.nextInt() % 10);
	/// System.out.println(newEst);
	/// System.out.println("Prediction for " + current 
	/// + " = " + newEst.getProbability(current));
	/// newEst.addValue(current, 1);
	/// }
	/// </pre> </code>
	/// 
	/// </summary>
	/// <author>  Len Trigg (trigg@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.5 $
	/// </version>
	public interface Estimator
	{
		/// <summary> Add a new data value to the current estimator.
		/// 
		/// </summary>
		/// <param name="data">the new data value 
		/// </param>
		/// <param name="weight">the weight assigned to the data value 
		/// </param>
		void  addValue(double data, double weight);
		
		/// <summary> Get a probability estimate for a value.
		/// 
		/// </summary>
		/// <param name="data">the value to estimate the probability of
		/// </param>
		/// <returns> the estimated probability of the supplied value
		/// </returns>
		double getProbability(double data);
	}
}