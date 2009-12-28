/*
*    ConditionalEstimator.java
*    Copyright (C) 1999 Len Trigg
*
*/
using System;
namespace weka.estimators
{
	
	/// <summary> Interface for conditional probability estimators. Example code: <p>
	/// 
	/// <code> <pre>
	/// NNConditionalEstimator newEst = new NNConditionalEstimator();
	/// 
	/// // Create 50 random points and add them
	/// Random r = new Random(seed);
	/// for(int i = 0; i < 50; i++) {
	/// int x = Math.abs(r.nextInt() % 100);
	/// int y = Math.abs(r.nextInt() % 100);
	/// System.out.println("# " + x + "  " + y);
	/// newEst.addValue(x, y, 1);
	/// }
	/// 
	/// // Pick a random conditional value
	/// int cond = Math.abs(r.nextInt() % 100);
	/// System.out.println("## Conditional = " + cond);
	/// 
	/// // Print the probabilities conditional on that value
	/// Estimator result = newEst.getEstimator(cond);
	/// for(int i = 0; i <= 100; i+= 5) {
	/// System.out.println(" " + i + "  " + result.getProbability(i));
	/// }
	/// </pre> </code>
	/// 
	/// </summary>
	/// <author>  Len Trigg (trigg@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.4 $
	/// </version>
	public interface ConditionalEstimator
	{
		/// <summary> Add a new data value to the current estimator.
		/// 
		/// </summary>
		/// <param name="data">the new data value 
		/// </param>
		/// <param name="given">the new value that data is conditional upon 
		/// </param>
		/// <param name="weight">the weight assigned to the data value 
		/// </param>
		void  addValue(double data, double given, double weight);
		
		/// <summary> Get a probability estimator for a value
		/// 
		/// </summary>
		/// <param name="given">the new value that data is conditional upon 
		/// </param>
		/// <returns> the estimator for the supplied value given the condition
		/// </returns>
		Estimator getEstimator(double given);
		
		/// <summary> Get a probability for a value conditional on another value
		/// 
		/// </summary>
		/// <param name="data">the value to estimate the probability of
		/// </param>
		/// <param name="given">the new value that data is conditional upon 
		/// </param>
		/// <returns> the estimator for the supplied value given the condition
		/// </returns>
		double getProbability(double data, double given);
	}
}