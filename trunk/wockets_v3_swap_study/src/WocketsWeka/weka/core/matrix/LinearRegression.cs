/*
* LinearRegression.java
* Copyright (C) 2005 University of Waikato, Hamilton, New Zealand
*
*/
using System;
using Utils = weka.core.Utils;
namespace weka.core.matrix
{
	
	/// <summary> Class for performing (ridged) linear regression.
	/// 
	/// </summary>
	/// <author>  Fracpete (fracpete at waikato dot ac dot nz)
	/// </author>
	/// <version>  $Revision: 1.2.2.2 $
	/// </version>
	
	public class LinearRegression
	{
		/// <summary> returns the calculated coefficients
		/// 
		/// </summary>
		/// <returns> the coefficients
		/// </returns>
		virtual public double[] Coefficients
		{
			get
			{
				return m_Coefficients;
			}
			
		}
		
		/// <summary>the coefficients </summary>
		protected internal double[] m_Coefficients = null;
		
		/// <summary> Performs a (ridged) linear regression.
		/// 
		/// </summary>
		/// <param name="a">the matrix to perform the regression on
		/// </param>
		/// <param name="y">the dependent variable vector
		/// </param>
		/// <param name="ridge">the ridge parameter
		/// </param>
		/// <returns> the coefficients 
		/// </returns>
		/// <throws>  IllegalArgumentException if not successful </throws>
		public LinearRegression(Matrix a, Matrix y, double ridge)
		{
			calculate(a, y, ridge);
		}
		
		/// <summary> Performs a weighted (ridged) linear regression. 
		/// 
		/// </summary>
		/// <param name="a">the matrix to perform the regression on
		/// </param>
		/// <param name="y">the dependent variable vector
		/// </param>
		/// <param name="w">the array of data point weights
		/// </param>
		/// <param name="ridge">the ridge parameter
		/// </param>
		/// <returns> the coefficients 
		/// </returns>
		/// <throws>  IllegalArgumentException if the wrong number of weights were </throws>
		/// <summary> provided.
		/// </summary>
		public LinearRegression(Matrix a, Matrix y, double[] w, double ridge)
		{
			
			if (w.Length != a.RowDimension)
				throw new System.ArgumentException("Incorrect number of weights provided");
			Matrix weightedThis = new Matrix(a.RowDimension, a.ColumnDimension);
			Matrix weightedDep = new Matrix(a.RowDimension, 1);
			for (int i = 0; i < w.Length; i++)
			{
				double sqrt_weight = System.Math.Sqrt(w[i]);
				for (int j = 0; j < a.ColumnDimension; j++)
					weightedThis.set_Renamed(i, j, a.get_Renamed(i, j) * sqrt_weight);
				weightedDep.set_Renamed(i, 0, y.get_Renamed(i, 0) * sqrt_weight);
			}
			
			calculate(weightedThis, weightedDep, ridge);
		}
		
		/// <summary> performs the actual regression.
		/// 
		/// </summary>
		/// <param name="a">the matrix to perform the regression on
		/// </param>
		/// <param name="y">the dependent variable vector
		/// </param>
		/// <param name="ridge">the ridge parameter
		/// </param>
		/// <returns> the coefficients 
		/// </returns>
		/// <throws>  IllegalArgumentException if not successful </throws>
		protected internal virtual void  calculate(Matrix a, Matrix y, double ridge)
		{
			
			if (y.ColumnDimension > 1)
				throw new System.ArgumentException("Only one dependent variable allowed");
			
			int nc = a.ColumnDimension;
			m_Coefficients = new double[nc];
			Matrix xt = a.transpose();
			Matrix solution;
			
			bool success = true;
			
			do 
			{
				Matrix ss = xt.times(a);
				
				// Set ridge regression adjustment
				for (int i = 0; i < nc; i++)
					ss.set_Renamed(i, i, ss.get_Renamed(i, i) + ridge);
				
				// Carry out the regression
				Matrix bb = xt.times(y);
				for (int i = 0; i < nc; i++)
					m_Coefficients[i] = bb.get_Renamed(i, 0);
				
				try
				{
					solution = ss.solve(new Matrix(m_Coefficients, m_Coefficients.Length));
					for (int i = 0; i < nc; i++)
						m_Coefficients[i] = solution.get_Renamed(i, 0);
					success = true;
				}
				catch (System.Exception ex)
				{
					ridge *= 10;
					success = false;
				}
			}
			while (!success);
		}
		
		/// <summary> returns the coefficients in a string representation</summary>
		public override System.String ToString()
		{
			return Utils.arrayToString(Coefficients);
		}
	}
}