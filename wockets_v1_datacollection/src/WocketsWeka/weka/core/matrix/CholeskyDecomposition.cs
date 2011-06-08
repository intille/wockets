/*
* CholeskyDecomposition.java
* Copyright (C) 1999 The Mathworks and NIST
*
*/
using System;
namespace weka.core.matrix
{
	
	/// <summary> Cholesky Decomposition.
	/// <P>
	/// For a symmetric, positive definite matrix A, the Cholesky decomposition is
	/// an lower triangular matrix L so that A = L*L'.
	/// <P>
	/// If the matrix is not symmetric or positive definite, the constructor
	/// returns a partial decomposition and sets an internal flag that may
	/// be queried by the isSPD() method.
	/// <p/>
	/// Adapted from the <a href="http://math.nist.gov/javanumerics/jama/" target="_blank">JAMA</a> package.
	/// 
	/// </summary>
	/// <author>  The Mathworks and NIST 
	/// </author>
	/// <author>  Fracpete (fracpete at waikato dot ac dot nz)
	/// </author>
	/// <version>  $Revision: 1.1.2.2 $
	/// </version>

	#if !PocketPC
	[Serializable]
#endif
	public class CholeskyDecomposition
	{
		/// <summary> Is the matrix symmetric and positive definite?</summary>
		/// <returns>     true if A is symmetric and positive definite.
		/// </returns>
		virtual public bool SPD
		{
			get
			{
				return isspd;
			}
			
		}
		
		/// <summary> Array for internal storage of decomposition.</summary>
		/// <serial> internal array storage.
		/// </serial>
		private double[][] L;
		
		/// <summary> Row and column dimension (square matrix).</summary>
		/// <serial> matrix dimension.
		/// </serial>
		private int n;
		
		/// <summary> Symmetric and positive definite flag.</summary>
		/// <serial> is symmetric and positive definite flag.
		/// </serial>
		private bool isspd;
		
		/// <summary> Cholesky algorithm for symmetric and positive definite matrix.
		/// 
		/// </summary>
		/// <param name="A">  Square, symmetric matrix.
		/// </param>
		/// <returns>     Structure to access L and isspd flag.
		/// </returns>
		public CholeskyDecomposition(Matrix Arg)
		{
			// Initialize.
			double[][] A = Arg.Array;
			n = Arg.RowDimension;
			L = new double[n][];
			for (int i = 0; i < n; i++)
			{
				L[i] = new double[n];
			}
			isspd = (Arg.ColumnDimension == n);
			// Main loop.
			for (int j = 0; j < n; j++)
			{
				double[] Lrowj = L[j];
				double d = 0.0;
				for (int k = 0; k < j; k++)
				{
					double[] Lrowk = L[k];
					double s = 0.0;
					for (int i = 0; i < k; i++)
					{
						s += Lrowk[i] * Lrowj[i];
					}
					Lrowj[k] = s = (A[j][k] - s) / L[k][k];
					d = d + s * s;
					isspd = isspd & (A[k][j] == A[j][k]);
				}
				d = A[j][j] - d;
				isspd = isspd & (d > 0.0);
				L[j][j] = System.Math.Sqrt(System.Math.Max(d, 0.0));
				for (int k = j + 1; k < n; k++)
				{
					L[j][k] = 0.0;
				}
			}
		}
		
		/// <summary> Return triangular factor.</summary>
		/// <returns>     L
		/// </returns>
		public virtual Matrix getL()
		{
			return new Matrix(L, n, n);
		}
		
		/// <summary> Solve A*X = B</summary>
		/// <param name="B">  A Matrix with as many rows as A and any number of columns.
		/// </param>
		/// <returns>     X so that L*L'*X = B
		/// </returns>
		/// <exception cref="IllegalArgumentException"> Matrix row dimensions must agree.
		/// </exception>
		/// <exception cref="RuntimeException"> Matrix is not symmetric positive definite.
		/// </exception>
		public virtual Matrix solve(Matrix B)
		{
			if (B.RowDimension != n)
			{
				throw new System.ArgumentException("Matrix row dimensions must agree.");
			}
			if (!isspd)
			{
				throw new System.SystemException("Matrix is not symmetric positive definite.");
			}
			
			// Copy right hand side.
			double[][] X = B.ArrayCopy;
			int nx = B.ColumnDimension;
			
			// Solve L*Y = B;
			for (int k = 0; k < n; k++)
			{
				for (int i = k + 1; i < n; i++)
				{
					for (int j = 0; j < nx; j++)
					{
						X[i][j] -= X[k][j] * L[i][k];
					}
				}
				for (int j = 0; j < nx; j++)
				{
					X[k][j] /= L[k][k];
				}
			}
			
			// Solve L'*X = Y;
			for (int k = n - 1; k >= 0; k--)
			{
				for (int j = 0; j < nx; j++)
				{
					X[k][j] /= L[k][k];
				}
				for (int i = 0; i < k; i++)
				{
					for (int j = 0; j < nx; j++)
					{
						X[i][j] -= X[k][j] * L[k][i];
					}
				}
			}
			return new Matrix(X, n, nx);
		}
	}
}