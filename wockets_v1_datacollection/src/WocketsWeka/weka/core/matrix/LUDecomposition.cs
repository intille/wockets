/*
* LUDecomposition.java
* Copyright (C) 1999 The Mathworks and NIST
*
*/
using System;
namespace weka.core.matrix
{
	
	/// <summary> LU Decomposition.
	/// <P>
	/// For an m-by-n matrix A with m &gt;= n, the LU decomposition is an m-by-n
	/// unit lower triangular matrix L, an n-by-n upper triangular matrix U, and a
	/// permutation vector piv of length m so that A(piv,:) = L*U.  If m &lt; n,
	/// then L is m-by-m and U is m-by-n.
	/// <P>
	/// The LU decompostion with pivoting always exists, even if the matrix is
	/// singular, so the constructor will never fail.  The primary use of the LU
	/// decomposition is in the solution of square systems of simultaneous linear
	/// equations.  This will fail if isNonsingular() returns false.
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
	public class LUDecomposition
	{
		/// <summary> Is the matrix nonsingular?</summary>
		/// <returns>     true if U, and hence A, is nonsingular.
		/// </returns>
		virtual public bool Nonsingular
		{
			get
			{
				for (int j = 0; j < n; j++)
				{
					if (LU[j][j] == 0)
						return false;
				}
				return true;
			}
			
		}
		/// <summary> Return lower triangular factor</summary>
		/// <returns>     L
		/// </returns>
		virtual public Matrix L
		{
			get
			{
				Matrix X = new Matrix(m, n);
				double[][] L = X.Array;
				for (int i = 0; i < m; i++)
				{
					for (int j = 0; j < n; j++)
					{
						if (i > j)
						{
							L[i][j] = LU[i][j];
						}
						else if (i == j)
						{
							L[i][j] = 1.0;
						}
						else
						{
							L[i][j] = 0.0;
						}
					}
				}
				return X;
			}
			
		}
		/// <summary> Return upper triangular factor</summary>
		/// <returns>     U
		/// </returns>
		virtual public Matrix U
		{
			get
			{
				Matrix X = new Matrix(n, n);
				double[][] U = X.Array;
				for (int i = 0; i < n; i++)
				{
					for (int j = 0; j < n; j++)
					{
						if (i <= j)
						{
							U[i][j] = LU[i][j];
						}
						else
						{
							U[i][j] = 0.0;
						}
					}
				}
				return X;
			}
			
		}
		/// <summary> Return pivot permutation vector</summary>
		/// <returns>     piv
		/// </returns>
		virtual public int[] Pivot
		{
			get
			{
				int[] p = new int[m];
				for (int i = 0; i < m; i++)
				{
					p[i] = piv[i];
				}
				return p;
			}
			
		}
		/// <summary> Return pivot permutation vector as a one-dimensional double array</summary>
		/// <returns>     (double) piv
		/// </returns>
		virtual public double[] DoublePivot
		{
			get
			{
				double[] vals = new double[m];
				for (int i = 0; i < m; i++)
				{
					vals[i] = (double) piv[i];
				}
				return vals;
			}
			
		}
		
		/// <summary> Array for internal storage of decomposition.</summary>
		/// <serial> internal array storage.
		/// </serial>
		private double[][] LU;
		
		/// <summary> Row and column dimensions, and pivot sign.</summary>
		/// <serial> column dimension.
		/// </serial>
		/// <serial> row dimension.
		/// </serial>
		/// <serial> pivot sign.
		/// </serial>
		private int m, n, pivsign;
		
		/// <summary> Internal storage of pivot vector.</summary>
		/// <serial> pivot vector.
		/// </serial>
		private int[] piv;
		
		/// <summary> LU Decomposition</summary>
		/// <param name="A">  Rectangular matrix
		/// </param>
		/// <returns>     Structure to access L, U and piv.
		/// </returns>
		public LUDecomposition(Matrix A)
		{
			
			// Use a "left-looking", dot-product, Crout/Doolittle algorithm.
			
			LU = A.ArrayCopy;
			m = A.RowDimension;
			n = A.ColumnDimension;
			piv = new int[m];
			for (int i = 0; i < m; i++)
			{
				piv[i] = i;
			}
			pivsign = 1;
			double[] LUrowi;
			double[] LUcolj = new double[m];
			
			// Outer loop.
			
			for (int j = 0; j < n; j++)
			{
				
				// Make a copy of the j-th column to localize references.
				
				for (int i = 0; i < m; i++)
				{
					LUcolj[i] = LU[i][j];
				}
				
				// Apply previous transformations.
				
				for (int i = 0; i < m; i++)
				{
					LUrowi = LU[i];
					
					// Most of the time is spent in the following dot product.
					
					int kmax = System.Math.Min(i, j);
					double s = 0.0;
					for (int k = 0; k < kmax; k++)
					{
						s += LUrowi[k] * LUcolj[k];
					}
					
					LUrowi[j] = LUcolj[i] -= s;
				}
				
				// Find pivot and exchange if necessary.
				
				int p = j;
				for (int i = j + 1; i < m; i++)
				{
					if (System.Math.Abs(LUcolj[i]) > System.Math.Abs(LUcolj[p]))
					{
						p = i;
					}
				}
				if (p != j)
				{
					for (int k = 0; k < n; k++)
					{
						double t = LU[p][k]; LU[p][k] = LU[j][k]; LU[j][k] = t;
					}
					int k2 = piv[p]; piv[p] = piv[j]; piv[j] = k2;
					pivsign = - pivsign;
				}
				
				// Compute multipliers.
				
				if (j < m & LU[j][j] != 0.0)
				{
					for (int i = j + 1; i < m; i++)
					{
						LU[i][j] /= LU[j][j];
					}
				}
			}
		}
		
		/// <summary> Determinant</summary>
		/// <returns>     det(A)
		/// </returns>
		/// <exception cref="IllegalArgumentException"> Matrix must be square
		/// </exception>
		public virtual double det()
		{
			if (m != n)
			{
				throw new System.ArgumentException("Matrix must be square.");
			}
			double d = (double) pivsign;
			for (int j = 0; j < n; j++)
			{
				d *= LU[j][j];
			}
			return d;
		}
		
		/// <summary> Solve A*X = B</summary>
		/// <param name="B">  A Matrix with as many rows as A and any number of columns.
		/// </param>
		/// <returns>     X so that L*U*X = B(piv,:)
		/// </returns>
		/// <exception cref="IllegalArgumentException">Matrix row dimensions must agree.
		/// </exception>
		/// <exception cref="RuntimeException"> Matrix is singular.
		/// </exception>
		public virtual Matrix solve(Matrix B)
		{
			if (B.RowDimension != m)
			{
				throw new System.ArgumentException("Matrix row dimensions must agree.");
			}
			if (!this.Nonsingular)
			{
				throw new System.SystemException("Matrix is singular.");
			}
			
			// Copy right hand side with pivoting
			int nx = B.ColumnDimension;
			Matrix Xmat = B.getMatrix(piv, 0, nx - 1);
			double[][] X = Xmat.Array;
			
			// Solve L*Y = B(piv,:)
			for (int k = 0; k < n; k++)
			{
				for (int i = k + 1; i < n; i++)
				{
					for (int j = 0; j < nx; j++)
					{
						X[i][j] -= X[k][j] * LU[i][k];
					}
				}
			}
			// Solve U*X = Y;
			for (int k = n - 1; k >= 0; k--)
			{
				for (int j = 0; j < nx; j++)
				{
					X[k][j] /= LU[k][k];
				}
				for (int i = 0; i < k; i++)
				{
					for (int j = 0; j < nx; j++)
					{
						X[i][j] -= X[k][j] * LU[i][k];
					}
				}
			}
			return Xmat;
		}
	}
}