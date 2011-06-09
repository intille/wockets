/*
* Matrix.java
* Copyright (C) 1999 The Mathworks and NIST and 2005 University of Waikato,
*               Hamilton, New Zealand
*
*/
using System;
using WocketsWeka.Utils;
namespace weka.core.matrix
{
	
	/// <summary> Jama = Java Matrix class.
	/// <P>
	/// The Java Matrix Class provides the fundamental operations of numerical linear
	/// algebra.  Various constructors create Matrices from two dimensional arrays of
	/// double precision floating point numbers.  Various "gets" and "sets" provide
	/// access to submatrices and matrix elements.  Several methods implement basic
	/// matrix arithmetic, including matrix addition and multiplication, matrix
	/// norms, and element-by-element array operations.  Methods for reading and
	/// printing matrices are also included.  All the operations in this version of
	/// the Matrix Class involve real matrices.  Complex matrices may be handled in a
	/// future version.
	/// <P>
	/// Five fundamental matrix decompositions, which consist of pairs or triples of
	/// matrices, permutation vectors, and the like, produce results in five
	/// decomposition classes.  These decompositions are accessed by the Matrix class
	/// to compute solutions of simultaneous linear equations, determinants, inverses
	/// and other matrix functions.  The five decompositions are:
	/// <P>
	/// <UL>
	/// <LI>Cholesky Decomposition of symmetric, positive definite matrices.
	/// <LI>LU Decomposition of rectangular matrices.
	/// <LI>QR Decomposition of rectangular matrices.
	/// <LI>Singular Value Decomposition of rectangular matrices.
	/// <LI>Eigenvalue Decomposition of both symmetric and nonsymmetric square matrices.
	/// </UL>
	/// <DL>
	/// <DT><B>Example of use:</B></DT>
	/// <P>
	/// <DD>Solve a linear system A x = b and compute the residual norm, ||b - A x||.
	/// <P><PRE>
	/// double[][] vals = {{1.,2.,3},{4.,5.,6.},{7.,8.,10.}};
	/// Matrix A = new Matrix(vals);
	/// Matrix b = Matrix.random(3,1);
	/// Matrix x = A.solve(b);
	/// Matrix r = A.times(x).minus(b);
	/// double rnorm = r.normInf();
	/// </PRE></DD>
	/// </DL>
	/// <p/>
	/// Adapted from the <a href="http://math.nist.gov/javanumerics/jama/" target="_blank">JAMA</a> package. Additional methods are tagged with the 
	/// </summary>
	/// <author> </code> tag.
	/// 
	/// </author>
	/// <author>  The Mathworks and NIST 
	/// </author>
	/// <author>  Fracpete (fracpete at waikato dot ac dot nz)
	/// </author>
	/// <version>  $Revision: 1.2.2.4 $
	/// </version>
#if !PocketPC	
	[Serializable]
#endif
	public class Matrix : System.ICloneable
	{
		/// <summary> Access the internal two-dimensional array.</summary>
		/// <returns>     Pointer to the two-dimensional array of matrix elements.
		/// </returns>
		virtual public double[][] Array
		{
			get
			{
				return A;
			}
			
		}
		/// <summary> Copy the internal two-dimensional array.</summary>
		/// <returns>     Two-dimensional array copy of matrix elements.
		/// </returns>
		virtual public double[][] ArrayCopy
		{
			get
			{
				double[][] C = new double[m][];
				for (int i = 0; i < m; i++)
				{
					C[i] = new double[n];
				}
				for (int i = 0; i < m; i++)
				{
					for (int j = 0; j < n; j++)
					{
						C[i][j] = A[i][j];
					}
				}
				return C;
			}
			
		}
		/// <summary> Make a one-dimensional column packed copy of the internal array.</summary>
		/// <returns>     Matrix elements packed in a one-dimensional array by columns.
		/// </returns>
		virtual public double[] ColumnPackedCopy
		{
			get
			{
				double[] vals = new double[m * n];
				for (int i = 0; i < m; i++)
				{
					for (int j = 0; j < n; j++)
					{
						vals[i + j * m] = A[i][j];
					}
				}
				return vals;
			}
			
		}
		/// <summary> Make a one-dimensional row packed copy of the internal array.</summary>
		/// <returns>     Matrix elements packed in a one-dimensional array by rows.
		/// </returns>
		virtual public double[] RowPackedCopy
		{
			get
			{
				double[] vals = new double[m * n];
				for (int i = 0; i < m; i++)
				{
					for (int j = 0; j < n; j++)
					{
						vals[i * n + j] = A[i][j];
					}
				}
				return vals;
			}
			
		}
		/// <summary> Get row dimension.</summary>
		/// <returns>     m, the number of rows.
		/// </returns>
		virtual public int RowDimension
		{
			get
			{
				return m;
			}
			
		}
		/// <summary> Get column dimension.</summary>
		/// <returns>     n, the number of columns.
		/// </returns>
		virtual public int ColumnDimension
		{
			get
			{
				return n;
			}
			
		}
		/// <summary> Returns true if the matrix is symmetric.
		/// 
		/// </summary>
		/// <returns> boolean true if matrix is symmetric.
		/// </returns>
		/// <author>  FracPete, taken from old weka.core.Matrix class
		/// </author>
		virtual public bool Symmetric
		{
			get
			{
				int nr = A.Length, nc = A[0].Length;
				if (nr != nc)
					return false;
				
				for (int i = 0; i < nc; i++)
				{
					for (int j = 0; j < i; j++)
					{
						if (A[i][j] != A[j][i])
							return false;
					}
				}
				return true;
			}
			
		}
		/// <summary> returns whether the matrix is a square matrix or not.
		/// 
		/// </summary>
		/// <returns> true if the matrix is a square matrix
		/// </returns>
		/// <author>  FracPete
		/// </author>
		virtual public bool Square
		{
			get
			{
				return (RowDimension == ColumnDimension);
			}
			
		}
		
		/// <summary> Array for internal storage of elements.</summary>
		/// <serial> internal array storage.
		/// </serial>
		private double[][] A;
		
		/// <summary> Row and column dimensions.</summary>
		/// <serial> row dimension.
		/// </serial>
		/// <serial> column dimension.
		/// </serial>
		private int m, n;
		
		/// <summary> Construct an m-by-n matrix of zeros. </summary>
		/// <param name="m">   Number of rows.
		/// </param>
		/// <param name="n">   Number of colums.
		/// </param>
		public Matrix(int m, int n)
		{
			this.m = m;
			this.n = n;
			A = new double[m][];
			for (int i = 0; i < m; i++)
			{
				A[i] = new double[n];
			}
		}
		
		/// <summary> Construct an m-by-n constant matrix.</summary>
		/// <param name="m">   Number of rows.
		/// </param>
		/// <param name="n">   Number of colums.
		/// </param>
		/// <param name="s">   Fill the matrix with this scalar value.
		/// </param>
		public Matrix(int m, int n, double s)
		{
			this.m = m;
			this.n = n;
			A = new double[m][];
			for (int i = 0; i < m; i++)
			{
				A[i] = new double[n];
			}
			for (int i = 0; i < m; i++)
			{
				for (int j = 0; j < n; j++)
				{
					A[i][j] = s;
				}
			}
		}
		
		/// <summary> Construct a matrix from a 2-D array.</summary>
		/// <param name="A">   Two-dimensional array of doubles.
		/// </param>
		/// <exception cref="IllegalArgumentException">All rows must have the same length
		/// </exception>
		/// <seealso cref="constructWithCopy">
		/// </seealso>
		public Matrix(double[][] A)
		{
			m = A.Length;
			n = A[0].Length;
			for (int i = 0; i < m; i++)
			{
				if (A[i].Length != n)
				{
					throw new System.ArgumentException("All rows must have the same length.");
				}
			}
			this.A = A;
		}
		
		/// <summary> Construct a matrix quickly without checking arguments.</summary>
		/// <param name="A">   Two-dimensional array of doubles.
		/// </param>
		/// <param name="m">   Number of rows.
		/// </param>
		/// <param name="n">   Number of colums.
		/// </param>
		public Matrix(double[][] A, int m, int n)
		{
			this.A = A;
			this.m = m;
			this.n = n;
		}
		
		/// <summary> Construct a matrix from a one-dimensional packed array</summary>
		/// <param name="vals">One-dimensional array of doubles, packed by columns (ala
		/// Fortran).
		/// </param>
		/// <param name="m">   Number of rows.
		/// </param>
		/// <exception cref="IllegalArgumentException">Array length must be a multiple of m.
		/// </exception>
		public Matrix(double[] vals, int m)
		{
			this.m = m;
			n = (m != 0?vals.Length / m:0);
			if (m * n != vals.Length)
			{
				throw new System.ArgumentException("Array length must be a multiple of m.");
			}
			A = new double[m][];
			for (int i = 0; i < m; i++)
			{
				A[i] = new double[n];
			}
			for (int i = 0; i < m; i++)
			{
				for (int j = 0; j < n; j++)
				{
					A[i][j] = vals[i + j * m];
				}
			}
		}
		
		/// <summary> Reads a matrix from a reader. The first line in the file should
		/// contain the number of rows and columns. Subsequent lines
		/// contain elements of the matrix.
		/// 
		/// </summary>
		/// <param name="r">the reader containing the matrix
		/// </param>
		/// <throws>     Exception if an error occurs </throws>
		/// <seealso cref="write(Writer)">
		/// </seealso>
		/// <author>     FracPete, taken from old weka.core.Matrix class
		/// </author>
		//UPGRADE_ISSUE: Class hierarchy differences between 'java.io.Reader' and 'System.IO.StreamReader' may cause compilation errors. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1186'"
		public Matrix(System.IO.StreamReader r)
		{
			System.IO.StreamReader lnr = new System.IO.StreamReader(r.BaseStream, r.CurrentEncoding);
			System.String line;
			int currentRow = - 1;
			
			//UPGRADE_WARNING: Method 'java.io.LineNumberReader.readLine' was converted to 'System.IO.StreamReader.ReadLine' which may throw an exception. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1101'"
			while ((line = lnr.ReadLine()) != null)
			{
				
				// Comments
				if (line.StartsWith("%"))
					continue;
				
				Tokenizer st = new Tokenizer(line);
				// Ignore blank lines
				if (!st.HasMoreTokens())
					continue;
				
				if (currentRow < 0)
				{
					int rows = System.Int32.Parse(st.NextToken());
					if (!st.HasMoreTokens())
					{
						//UPGRADE_ISSUE: Method 'java.io.LineNumberReader.getLineNumber' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javaioLineNumberReadergetLineNumber'"
						throw new System.Exception("Line " + currentRow + ": expected number of columns");
					}
					
					int cols = System.Int32.Parse(st.NextToken());
					double[][] tmpArray = new double[rows][];
					for (int i = 0; i < rows; i++)
					{
						tmpArray[i] = new double[cols];
					}
					A = tmpArray;
					m = rows;
					n = cols;
					currentRow++;
					continue;
				}
				else
				{
					if (currentRow == RowDimension)
					{
						//UPGRADE_ISSUE: Method 'java.io.LineNumberReader.getLineNumber' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javaioLineNumberReadergetLineNumber'"
                        throw new System.Exception("Line " + currentRow + ": too many rows provided");
					}
					
					for (int i = 0; i < ColumnDimension; i++)
					{
						if (!st.HasMoreTokens())
						{
							//UPGRADE_ISSUE: Method 'java.io.LineNumberReader.getLineNumber' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javaioLineNumberReadergetLineNumber'"
                            throw new System.Exception("Line " + currentRow + ": too few matrix elements provided");
						}
						
						set_Renamed(currentRow, i, System.Double.Parse(st.NextToken()));
					}
					currentRow++;
				}
			}
			
			if (currentRow == - 1)
			{
				//UPGRADE_ISSUE: Method 'java.io.LineNumberReader.getLineNumber' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javaioLineNumberReadergetLineNumber'"
                throw new System.Exception("Line " + currentRow + ": expected number of rows");
			}
			else if (currentRow != RowDimension)
			{
				//UPGRADE_ISSUE: Method 'java.io.LineNumberReader.getLineNumber' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javaioLineNumberReadergetLineNumber'"
                throw new System.Exception("Line " + currentRow + ": too few rows provided");
			}
		}
		
		/// <summary> Construct a matrix from a copy of a 2-D array.</summary>
		/// <param name="A">   Two-dimensional array of doubles.
		/// </param>
		/// <exception cref="IllegalArgumentException">All rows must have the same length
		/// </exception>
		public static Matrix constructWithCopy(double[][] A)
		{
			int m = A.Length;
			int n = A[0].Length;
			Matrix X = new Matrix(m, n);
			double[][] C = X.Array;
			for (int i = 0; i < m; i++)
			{
				if (A[i].Length != n)
				{
					throw new System.ArgumentException("All rows must have the same length.");
				}
				for (int j = 0; j < n; j++)
				{
					C[i][j] = A[i][j];
				}
			}
			return X;
		}
		
		/// <summary> Make a deep copy of a matrix</summary>
		public virtual Matrix copy()
		{
			Matrix X = new Matrix(m, n);
			double[][] C = X.Array;
			for (int i = 0; i < m; i++)
			{
				for (int j = 0; j < n; j++)
				{
					C[i][j] = A[i][j];
				}
			}
			return X;
		}
		
		/// <summary> Clone the Matrix object.</summary>
		public virtual System.Object Clone()
		{
			return this.copy();
		}
		
		/// <summary> Get a single element.</summary>
		/// <param name="i">   Row index.
		/// </param>
		/// <param name="j">   Column index.
		/// </param>
		/// <returns>     A(i,j)
		/// </returns>
		/// <exception cref="ArrayIndexOutOfBoundsException">
		/// </exception>
		public virtual double get_Renamed(int i, int j)
		{
			return A[i][j];
		}
		
		/// <summary> Get a submatrix.</summary>
		/// <param name="i0">  Initial row index
		/// </param>
		/// <param name="i1">  Final row index
		/// </param>
		/// <param name="j0">  Initial column index
		/// </param>
		/// <param name="j1">  Final column index
		/// </param>
		/// <returns>     A(i0:i1,j0:j1)
		/// </returns>
		/// <exception cref="ArrayIndexOutOfBoundsException">Submatrix indices
		/// </exception>
		public virtual Matrix getMatrix(int i0, int i1, int j0, int j1)
		{
			Matrix X = new Matrix(i1 - i0 + 1, j1 - j0 + 1);
			double[][] B = X.Array;
			try
			{
				for (int i = i0; i <= i1; i++)
				{
					for (int j = j0; j <= j1; j++)
					{
						B[i - i0][j - j0] = A[i][j];
					}
				}
			}
			catch (System.IndexOutOfRangeException e)
			{
				throw new System.IndexOutOfRangeException("Submatrix indices");
			}
			return X;
		}
		
		/// <summary> Get a submatrix.</summary>
		/// <param name="r">   Array of row indices.
		/// </param>
		/// <param name="c">   Array of column indices.
		/// </param>
		/// <returns>     A(r(:),c(:))
		/// </returns>
		/// <exception cref="ArrayIndexOutOfBoundsException">Submatrix indices
		/// </exception>
		public virtual Matrix getMatrix(int[] r, int[] c)
		{
			Matrix X = new Matrix(r.Length, c.Length);
			double[][] B = X.Array;
			try
			{
				for (int i = 0; i < r.Length; i++)
				{
					for (int j = 0; j < c.Length; j++)
					{
						B[i][j] = A[r[i]][c[j]];
					}
				}
			}
			catch (System.IndexOutOfRangeException e)
			{
				throw new System.IndexOutOfRangeException("Submatrix indices");
			}
			return X;
		}
		
		/// <summary> Get a submatrix.</summary>
		/// <param name="i0">  Initial row index
		/// </param>
		/// <param name="i1">  Final row index
		/// </param>
		/// <param name="c">   Array of column indices.
		/// </param>
		/// <returns>     A(i0:i1,c(:))
		/// </returns>
		/// <exception cref="ArrayIndexOutOfBoundsException">Submatrix indices
		/// </exception>
		public virtual Matrix getMatrix(int i0, int i1, int[] c)
		{
			Matrix X = new Matrix(i1 - i0 + 1, c.Length);
			double[][] B = X.Array;
			try
			{
				for (int i = i0; i <= i1; i++)
				{
					for (int j = 0; j < c.Length; j++)
					{
						B[i - i0][j] = A[i][c[j]];
					}
				}
			}
			catch (System.IndexOutOfRangeException e)
			{
				throw new System.IndexOutOfRangeException("Submatrix indices");
			}
			return X;
		}
		
		/// <summary> Get a submatrix.</summary>
		/// <param name="r">   Array of row indices.
		/// </param>
		/// <param name="i0">  Initial column index
		/// </param>
		/// <param name="i1">  Final column index
		/// </param>
		/// <returns>     A(r(:),j0:j1)
		/// </returns>
		/// <exception cref="ArrayIndexOutOfBoundsException">Submatrix indices
		/// </exception>
		public virtual Matrix getMatrix(int[] r, int j0, int j1)
		{
			Matrix X = new Matrix(r.Length, j1 - j0 + 1);
			double[][] B = X.Array;
			try
			{
				for (int i = 0; i < r.Length; i++)
				{
					for (int j = j0; j <= j1; j++)
					{
						B[i][j - j0] = A[r[i]][j];
					}
				}
			}
			catch (System.IndexOutOfRangeException e)
			{
				throw new System.IndexOutOfRangeException("Submatrix indices");
			}
			return X;
		}
		
		/// <summary> Set a single element.</summary>
		/// <param name="i">   Row index.
		/// </param>
		/// <param name="j">   Column index.
		/// </param>
		/// <param name="s">   A(i,j).
		/// </param>
		/// <exception cref="ArrayIndexOutOfBoundsException">
		/// </exception>
		public virtual void  set_Renamed(int i, int j, double s)
		{
			A[i][j] = s;
		}
		
		/// <summary> Set a submatrix.</summary>
		/// <param name="i0">  Initial row index
		/// </param>
		/// <param name="i1">  Final row index
		/// </param>
		/// <param name="j0">  Initial column index
		/// </param>
		/// <param name="j1">  Final column index
		/// </param>
		/// <param name="X">   A(i0:i1,j0:j1)
		/// </param>
		/// <exception cref="ArrayIndexOutOfBoundsException">Submatrix indices
		/// </exception>
		public virtual void  setMatrix(int i0, int i1, int j0, int j1, Matrix X)
		{
			try
			{
				for (int i = i0; i <= i1; i++)
				{
					for (int j = j0; j <= j1; j++)
					{
						A[i][j] = X.get_Renamed(i - i0, j - j0);
					}
				}
			}
			catch (System.IndexOutOfRangeException e)
			{
				throw new System.IndexOutOfRangeException("Submatrix indices");
			}
		}
		
		/// <summary> Set a submatrix.</summary>
		/// <param name="r">   Array of row indices.
		/// </param>
		/// <param name="c">   Array of column indices.
		/// </param>
		/// <param name="X">   A(r(:),c(:))
		/// </param>
		/// <exception cref="ArrayIndexOutOfBoundsException">Submatrix indices
		/// </exception>
		public virtual void  setMatrix(int[] r, int[] c, Matrix X)
		{
			try
			{
				for (int i = 0; i < r.Length; i++)
				{
					for (int j = 0; j < c.Length; j++)
					{
						A[r[i]][c[j]] = X.get_Renamed(i, j);
					}
				}
			}
			catch (System.IndexOutOfRangeException e)
			{
				throw new System.IndexOutOfRangeException("Submatrix indices");
			}
		}
		
		/// <summary> Set a submatrix.</summary>
		/// <param name="r">   Array of row indices.
		/// </param>
		/// <param name="j0">  Initial column index
		/// </param>
		/// <param name="j1">  Final column index
		/// </param>
		/// <param name="X">   A(r(:),j0:j1)
		/// </param>
		/// <exception cref="ArrayIndexOutOfBoundsException">Submatrix indices
		/// </exception>
		public virtual void  setMatrix(int[] r, int j0, int j1, Matrix X)
		{
			try
			{
				for (int i = 0; i < r.Length; i++)
				{
					for (int j = j0; j <= j1; j++)
					{
						A[r[i]][j] = X.get_Renamed(i, j - j0);
					}
				}
			}
			catch (System.IndexOutOfRangeException e)
			{
				throw new System.IndexOutOfRangeException("Submatrix indices");
			}
		}
		
		/// <summary> Set a submatrix.</summary>
		/// <param name="i0">  Initial row index
		/// </param>
		/// <param name="i1">  Final row index
		/// </param>
		/// <param name="c">   Array of column indices.
		/// </param>
		/// <param name="X">   A(i0:i1,c(:))
		/// </param>
		/// <exception cref="ArrayIndexOutOfBoundsException">Submatrix indices
		/// </exception>
		public virtual void  setMatrix(int i0, int i1, int[] c, Matrix X)
		{
			try
			{
				for (int i = i0; i <= i1; i++)
				{
					for (int j = 0; j < c.Length; j++)
					{
						A[i][c[j]] = X.get_Renamed(i - i0, j);
					}
				}
			}
			catch (System.IndexOutOfRangeException e)
			{
				throw new System.IndexOutOfRangeException("Submatrix indices");
			}
		}
		
		/// <summary> Matrix transpose.</summary>
		/// <returns>    A'
		/// </returns>
		public virtual Matrix transpose()
		{
			Matrix X = new Matrix(n, m);
			double[][] C = X.Array;
			for (int i = 0; i < m; i++)
			{
				for (int j = 0; j < n; j++)
				{
					C[j][i] = A[i][j];
				}
			}
			return X;
		}
		
		/// <summary> One norm</summary>
		/// <returns>    maximum column sum.
		/// </returns>
		public virtual double norm1()
		{
			double f = 0;
			for (int j = 0; j < n; j++)
			{
				double s = 0;
				for (int i = 0; i < m; i++)
				{
					s += System.Math.Abs(A[i][j]);
				}
				f = System.Math.Max(f, s);
			}
			return f;
		}
		
		/// <summary> Two norm</summary>
		/// <returns>    maximum singular value.
		/// </returns>
		public virtual double norm2()
		{
			return (new SingularValueDecomposition(this).norm2());
		}
		
		/// <summary> Infinity norm</summary>
		/// <returns>    maximum row sum.
		/// </returns>
		public virtual double normInf()
		{
			double f = 0;
			for (int i = 0; i < m; i++)
			{
				double s = 0;
				for (int j = 0; j < n; j++)
				{
					s += System.Math.Abs(A[i][j]);
				}
				f = System.Math.Max(f, s);
			}
			return f;
		}
		
		/// <summary> Frobenius norm</summary>
		/// <returns>    sqrt of sum of squares of all elements.
		/// </returns>
		public virtual double normF()
		{
			double f = 0;
			for (int i = 0; i < m; i++)
			{
				for (int j = 0; j < n; j++)
				{
					f = Maths.hypot(f, A[i][j]);
				}
			}
			return f;
		}
		
		/// <summary> Unary minus</summary>
		/// <returns>    -A
		/// </returns>
		public virtual Matrix uminus()
		{
			Matrix X = new Matrix(m, n);
			double[][] C = X.Array;
			for (int i = 0; i < m; i++)
			{
				for (int j = 0; j < n; j++)
				{
					C[i][j] = - A[i][j];
				}
			}
			return X;
		}
		
		/// <summary> C = A + B</summary>
		/// <param name="B">   another matrix
		/// </param>
		/// <returns>     A + B
		/// </returns>
		public virtual Matrix plus(Matrix B)
		{
			checkMatrixDimensions(B);
			Matrix X = new Matrix(m, n);
			double[][] C = X.Array;
			for (int i = 0; i < m; i++)
			{
				for (int j = 0; j < n; j++)
				{
					C[i][j] = A[i][j] + B.A[i][j];
				}
			}
			return X;
		}
		
		/// <summary> A = A + B</summary>
		/// <param name="B">   another matrix
		/// </param>
		/// <returns>     A + B
		/// </returns>
		public virtual Matrix plusEquals(Matrix B)
		{
			checkMatrixDimensions(B);
			for (int i = 0; i < m; i++)
			{
				for (int j = 0; j < n; j++)
				{
					A[i][j] = A[i][j] + B.A[i][j];
				}
			}
			return this;
		}
		
		/// <summary> C = A - B</summary>
		/// <param name="B">   another matrix
		/// </param>
		/// <returns>     A - B
		/// </returns>
		public virtual Matrix minus(Matrix B)
		{
			checkMatrixDimensions(B);
			Matrix X = new Matrix(m, n);
			double[][] C = X.Array;
			for (int i = 0; i < m; i++)
			{
				for (int j = 0; j < n; j++)
				{
					C[i][j] = A[i][j] - B.A[i][j];
				}
			}
			return X;
		}
		
		/// <summary> A = A - B</summary>
		/// <param name="B">   another matrix
		/// </param>
		/// <returns>     A - B
		/// </returns>
		public virtual Matrix minusEquals(Matrix B)
		{
			checkMatrixDimensions(B);
			for (int i = 0; i < m; i++)
			{
				for (int j = 0; j < n; j++)
				{
					A[i][j] = A[i][j] - B.A[i][j];
				}
			}
			return this;
		}
		
		/// <summary> XmlElement-by-element multiplication, C = A.*B</summary>
		/// <param name="B">   another matrix
		/// </param>
		/// <returns>     A.*B
		/// </returns>
		public virtual Matrix arrayTimes(Matrix B)
		{
			checkMatrixDimensions(B);
			Matrix X = new Matrix(m, n);
			double[][] C = X.Array;
			for (int i = 0; i < m; i++)
			{
				for (int j = 0; j < n; j++)
				{
					C[i][j] = A[i][j] * B.A[i][j];
				}
			}
			return X;
		}
		
		/// <summary> XmlElement-by-element multiplication in place, A = A.*B</summary>
		/// <param name="B">   another matrix
		/// </param>
		/// <returns>     A.*B
		/// </returns>
		public virtual Matrix arrayTimesEquals(Matrix B)
		{
			checkMatrixDimensions(B);
			for (int i = 0; i < m; i++)
			{
				for (int j = 0; j < n; j++)
				{
					A[i][j] = A[i][j] * B.A[i][j];
				}
			}
			return this;
		}
		
		/// <summary> XmlElement-by-element right division, C = A./B</summary>
		/// <param name="B">   another matrix
		/// </param>
		/// <returns>     A./B
		/// </returns>
		public virtual Matrix arrayRightDivide(Matrix B)
		{
			checkMatrixDimensions(B);
			Matrix X = new Matrix(m, n);
			double[][] C = X.Array;
			for (int i = 0; i < m; i++)
			{
				for (int j = 0; j < n; j++)
				{
					C[i][j] = A[i][j] / B.A[i][j];
				}
			}
			return X;
		}
		
		/// <summary> XmlElement-by-element right division in place, A = A./B</summary>
		/// <param name="B">   another matrix
		/// </param>
		/// <returns>     A./B
		/// </returns>
		public virtual Matrix arrayRightDivideEquals(Matrix B)
		{
			checkMatrixDimensions(B);
			for (int i = 0; i < m; i++)
			{
				for (int j = 0; j < n; j++)
				{
					A[i][j] = A[i][j] / B.A[i][j];
				}
			}
			return this;
		}
		
		/// <summary> XmlElement-by-element left division, C = A.\B</summary>
		/// <param name="B">   another matrix
		/// </param>
		/// <returns>     A.\B
		/// </returns>
		public virtual Matrix arrayLeftDivide(Matrix B)
		{
			checkMatrixDimensions(B);
			Matrix X = new Matrix(m, n);
			double[][] C = X.Array;
			for (int i = 0; i < m; i++)
			{
				for (int j = 0; j < n; j++)
				{
					C[i][j] = B.A[i][j] / A[i][j];
				}
			}
			return X;
		}
		
		/// <summary> XmlElement-by-element left division in place, A = A.\B</summary>
		/// <param name="B">   another matrix
		/// </param>
		/// <returns>     A.\B
		/// </returns>
		public virtual Matrix arrayLeftDivideEquals(Matrix B)
		{
			checkMatrixDimensions(B);
			for (int i = 0; i < m; i++)
			{
				for (int j = 0; j < n; j++)
				{
					A[i][j] = B.A[i][j] / A[i][j];
				}
			}
			return this;
		}
		
		/// <summary> Multiply a matrix by a scalar, C = s*A</summary>
		/// <param name="s">   scalar
		/// </param>
		/// <returns>     s*A
		/// </returns>
		public virtual Matrix times(double s)
		{
			Matrix X = new Matrix(m, n);
			double[][] C = X.Array;
			for (int i = 0; i < m; i++)
			{
				for (int j = 0; j < n; j++)
				{
					C[i][j] = s * A[i][j];
				}
			}
			return X;
		}
		
		/// <summary> Multiply a matrix by a scalar in place, A = s*A</summary>
		/// <param name="s">   scalar
		/// </param>
		/// <returns>     replace A by s*A
		/// </returns>
		public virtual Matrix timesEquals(double s)
		{
			for (int i = 0; i < m; i++)
			{
				for (int j = 0; j < n; j++)
				{
					A[i][j] = s * A[i][j];
				}
			}
			return this;
		}
		
		/// <summary> Linear algebraic matrix multiplication, A * B</summary>
		/// <param name="B">   another matrix
		/// </param>
		/// <returns>     Matrix product, A * B
		/// </returns>
		/// <exception cref="IllegalArgumentException">Matrix inner dimensions must agree.
		/// </exception>
		public virtual Matrix times(Matrix B)
		{
			if (B.m != n)
			{
				throw new System.ArgumentException("Matrix inner dimensions must agree.");
			}
			Matrix X = new Matrix(m, B.n);
			double[][] C = X.Array;
			double[] Bcolj = new double[n];
			for (int j = 0; j < B.n; j++)
			{
				for (int k = 0; k < n; k++)
				{
					Bcolj[k] = B.A[k][j];
				}
				for (int i = 0; i < m; i++)
				{
					double[] Arowi = A[i];
					double s = 0;
					for (int k = 0; k < n; k++)
					{
						s += Arowi[k] * Bcolj[k];
					}
					C[i][j] = s;
				}
			}
			return X;
		}
		
		/// <summary> LU Decomposition</summary>
		/// <returns>     LUDecomposition
		/// </returns>
		/// <seealso cref="LUDecomposition">
		/// </seealso>
		public virtual LUDecomposition lu()
		{
			return new LUDecomposition(this);
		}
		
		/// <summary> QR Decomposition</summary>
		/// <returns>     QRDecomposition
		/// </returns>
		/// <seealso cref="QRDecomposition">
		/// </seealso>
		public virtual QRDecomposition qr()
		{
			return new QRDecomposition(this);
		}
		
		/// <summary> Cholesky Decomposition</summary>
		/// <returns>     CholeskyDecomposition
		/// </returns>
		/// <seealso cref="CholeskyDecomposition">
		/// </seealso>
		public virtual CholeskyDecomposition chol()
		{
			return new CholeskyDecomposition(this);
		}
		
		/// <summary> Singular Value Decomposition</summary>
		/// <returns>     SingularValueDecomposition
		/// </returns>
		/// <seealso cref="SingularValueDecomposition">
		/// </seealso>
		public virtual SingularValueDecomposition svd()
		{
			return new SingularValueDecomposition(this);
		}
		
		/// <summary> Eigenvalue Decomposition</summary>
		/// <returns>     EigenvalueDecomposition
		/// </returns>
		/// <seealso cref="EigenvalueDecomposition">
		/// </seealso>
		public virtual EigenvalueDecomposition eig()
		{
			return new EigenvalueDecomposition(this);
		}
		
		/// <summary> Solve A*X = B</summary>
		/// <param name="B">   right hand side
		/// </param>
		/// <returns>     solution if A is square, least squares solution otherwise
		/// </returns>
		public virtual Matrix solve(Matrix B)
		{
			return (m == n?(new LUDecomposition(this)).solve(B):(new QRDecomposition(this)).solve(B));
		}
		
		/// <summary> Solve X*A = B, which is also A'*X' = B'</summary>
		/// <param name="B">   right hand side
		/// </param>
		/// <returns>     solution if A is square, least squares solution otherwise.
		/// </returns>
		public virtual Matrix solveTranspose(Matrix B)
		{
			return transpose().solve(B.transpose());
		}
		
		/// <summary> Matrix inverse or pseudoinverse</summary>
		/// <returns>     inverse(A) if A is square, pseudoinverse otherwise.
		/// </returns>
		public virtual Matrix inverse()
		{
			return solve(identity(m, m));
		}
		
		/// <summary> returns the square root of the matrix, i.e., X from the equation
		/// X*X = A.<br/>
		/// Steps in the Calculation (see <a href="http://www.mathworks.com/access/helpdesk/help/techdoc/ref/sqrtm.html" target="blank"><code>sqrtm</code></a> in Matlab):<br/>
		/// <ol>
		/// <li>perform eigenvalue decomposition<br/>[V,D]=eig(A)</li>
		/// <li>take the square root of all elements in D (only the ones with 
		/// positive sign are considered for further computation)<br/>
		/// S=sqrt(D)</li>
		/// <li>calculate the root<br/>
		/// X=V*S/V, which can be also written as X=(V'\(V*S)')'</li>
		/// </ol>
		/// <p/>
		/// <b>Note:</b> since this method uses other high-level methods, it generates
		/// several instances of matrices. This can be problematic with large
		/// matrices.
		/// <p/>
		/// Examples:
		/// <ol>
		/// <li>
		/// <pre>
		/// X =
		/// 5   -4    1    0    0
		/// -4    6   -4    1    0
		/// 1   -4    6   -4    1
		/// 0    1   -4    6   -4
		/// 0    0    1   -4    5
		/// 
		/// sqrt(X) =
		/// 2   -1   -0   -0   -0 
		/// -1    2   -1    0   -0 
		/// 0   -1    2   -1    0 
		/// -0    0   -1    2   -1 
		/// -0   -0   -0   -1    2 
		/// 
		/// Matrix m = new Matrix(new double[][]{{5,-4,1,0,0},{-4,6,-4,1,0},{1,-4,6,-4,1},{0,1,-4,6,-4},{0,0,1,-4,5}});
		/// </pre>
		/// </li>
		/// <li>
		/// <pre>
		/// X =
		/// 7   10
		/// 15   22
		/// 
		/// sqrt(X) =
		/// 1.5667    1.7408
		/// 2.6112    4.1779
		/// 
		/// Matrix m = new Matrix(new double[][]{{7, 10},{15, 22}});
		/// </pre>
		/// </li>
		/// </ol>
		/// 
		/// </summary>
		/// <returns>    sqrt(A)
		/// </returns>
		/// <author>     FracPete
		/// </author>
		public virtual Matrix sqrt()
		{
			EigenvalueDecomposition evd;
			Matrix s;
			Matrix v;
			Matrix d;
			Matrix result;
			Matrix a;
			Matrix b;
			int i;
			int n;
			
			result = null;
			
			// eigenvalue decomp.
			// [V, D] = eig(A) with A = this
			evd = this.eig();
			v = evd.getV();
			d = evd.D;
			
			// S = sqrt of cells of D
			s = new Matrix(d.RowDimension, d.ColumnDimension);
			for (i = 0; i < s.RowDimension; i++)
				for (n = 0; n < s.ColumnDimension; n++)
					s.set_Renamed(i, n, System.Math.Sqrt(d.get_Renamed(i, n)));
			
			// to calculate:
			//      result = V*S/V
			//
			//    with   X = B/A
			//    and  B/A = (A'\B')'
			//    and V=A and V*S=B
			// we get 
			//      result = (V'\(V*S)')'
			//      
			//         A*X = B
			//           X = A\B
			// which is 
			//           X = A.solve(B)
			//           
			// with A=V' and B=(V*S)' 
			// we get
			//           X = V'.solve((V*S)')
			// or
			//      result = X'
			//
			// which is in full length
			//      result = (V'.solve((V*S)'))'
			a = v.inverse();
			b = v.times(s).inverse();
			v = null;
			d = null;
			evd = null;
			s = null;
			result = a.solve(b).inverse();
			
			return result;
		}
		
		/// <summary> Performs a (ridged) linear regression.
		/// 
		/// </summary>
		/// <param name="y">the dependent variable vector
		/// </param>
		/// <param name="ridge">the ridge parameter
		/// </param>
		/// <returns>    the coefficients 
		/// </returns>
		/// <throws>     IllegalArgumentException if not successful </throws>
		/// <author>     FracPete, taken from old weka.core.Matrix class
		/// </author>
		public virtual LinearRegression regression(Matrix y, double ridge)
		{
			return new LinearRegression(this, y, ridge);
		}
		
		/// <summary> Performs a weighted (ridged) linear regression. 
		/// 
		/// </summary>
		/// <param name="y">the dependent variable vector
		/// </param>
		/// <param name="w">the array of data point weights
		/// </param>
		/// <param name="ridge">the ridge parameter
		/// </param>
		/// <returns>    the coefficients 
		/// </returns>
		/// <throws>     IllegalArgumentException if the wrong number of weights were </throws>
		/// <summary>            provided.
		/// </summary>
		/// <author>     FracPete, taken from old weka.core.Matrix class
		/// </author>
		public LinearRegression regression(Matrix y, double[] w, double ridge)
		{
			return new LinearRegression(this, y, w, ridge);
		}
		
		/// <summary> Matrix determinant</summary>
		/// <returns>     determinant
		/// </returns>
		public virtual double det()
		{
			return new LUDecomposition(this).det();
		}
		
		/// <summary> Matrix rank</summary>
		/// <returns>     effective numerical rank, obtained from SVD.
		/// </returns>
		public virtual int rank()
		{
			return new SingularValueDecomposition(this).rank();
		}
		
		/// <summary> Matrix condition (2 norm)</summary>
		/// <returns>     ratio of largest to smallest singular value.
		/// </returns>
		public virtual double cond()
		{
			return new SingularValueDecomposition(this).cond();
		}
		
		/// <summary> Matrix trace.</summary>
		/// <returns>     sum of the diagonal elements.
		/// </returns>
		public virtual double trace()
		{
			double t = 0;
			for (int i = 0; i < System.Math.Min(m, n); i++)
			{
				t += A[i][i];
			}
			return t;
		}
		
		/// <summary> Generate matrix with random elements</summary>
		/// <param name="m">   Number of rows.
		/// </param>
		/// <param name="n">   Number of colums.
		/// </param>
		/// <returns>     An m-by-n matrix with uniformly distributed random elements.
		/// </returns>
		public static Matrix random(int m, int n)
		{
			Matrix A = new Matrix(m, n);
			double[][] X = A.Array;
            Random r = new Random();
			for (int i = 0; i < m; i++)
			{
				for (int j = 0; j < n; j++)
				{
					X[i][j] = r.NextDouble();
				}
			}
			return A;
		}
		
		/// <summary> Generate identity matrix</summary>
		/// <param name="m">   Number of rows.
		/// </param>
		/// <param name="n">   Number of colums.
		/// </param>
		/// <returns>     An m-by-n matrix with ones on the diagonal and zeros elsewhere.
		/// </returns>
		public static Matrix identity(int m, int n)
		{
			Matrix A = new Matrix(m, n);
			double[][] X = A.Array;
			for (int i = 0; i < m; i++)
			{
				for (int j = 0; j < n; j++)
				{
					X[i][j] = (i == j?1.0:0.0);
				}
			}
			return A;
		}
		#if !PocketPC
		/// <summary> Print the matrix to stdout.   Line the elements up in columns
		/// with a Fortran-like 'Fw.d' style format.
		/// </summary>
		/// <param name="w">   Column width.
		/// </param>
		/// <param name="d">   Number of digits after the decimal.
		/// </param>
		public virtual void  print(int w, int d)
		{
			System.IO.StreamWriter temp_writer;
			temp_writer = new System.IO.StreamWriter(System.Console.OpenStandardOutput(), System.Text.Encoding.Default);
			temp_writer.AutoFlush = true;
			print(temp_writer, w, d);
		}
#endif
		
		/// <summary> Print the matrix to the output stream.   Line the elements up in
		/// columns with a Fortran-like 'Fw.d' style format.
		/// </summary>
		/// <param name="output">Output stream.
		/// </param>
		/// <param name="w">     Column width.
		/// </param>
		/// <param name="d">     Number of digits after the decimal.
		/// </param>
		public virtual void  print(System.IO.StreamWriter output, int w, int d)
		{
			//UPGRADE_ISSUE: Class 'java.text.DecimalFormat' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javatextDecimalFormat'"
			//UPGRADE_ISSUE: Constructor 'java.text.DecimalFormat.DecimalFormat' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javatextDecimalFormat'"
			//DecimalFormat format = new DecimalFormat();
			//UPGRADE_ISSUE: Method 'java.text.DecimalFormat.setDecimalFormatSymbols' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javatextDecimalFormat'"
			//format.setDecimalFormatSymbols(new System.Globalization.CultureInfo("en-US").NumberFormat);
			//UPGRADE_ISSUE: Method 'java.text.DecimalFormat.setMinimumIntegerDigits' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javatextDecimalFormat'"
			//format.setMinimumIntegerDigits(1);
			//UPGRADE_ISSUE: Method 'java.text.DecimalFormat.setMaximumFractionDigits' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javatextDecimalFormat'"
			//format.setMaximumFractionDigits(d);
			//UPGRADE_ISSUE: Method 'java.text.DecimalFormat.setMinimumFractionDigits' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javatextDecimalFormat'"
			//format.setMinimumFractionDigits(d);
			//format.GroupingUsed = false;
            TextNumberFormat format = new TextNumberFormat();
            format.Digits = d;
            format.GroupingUsed = false;
			print(output, format, w + 2);
		}
		#if !PocketPC
		/// <summary> Print the matrix to stdout.  Line the elements up in columns.
		/// Use the format object, and right justify within columns of width
		/// characters.
		/// Note that is the matrix is to be read back in, you probably will want
		/// to use a NumberFormat that is set to US Locale.
		/// </summary>
		/// <param name="format">A  Formatting object for individual elements.
		/// </param>
		/// <param name="width">    Field width for each column.
		/// </param>
		/// <seealso cref="java.text.DecimalFormat.setDecimalFormatSymbols">
		/// </seealso>
		public virtual void  print(TextNumberFormat format, int width)
		{
			System.IO.StreamWriter temp_writer;
			temp_writer = new System.IO.StreamWriter(System.Console.OpenStandardOutput(), System.Text.Encoding.Default);
			temp_writer.AutoFlush = true;
			print(temp_writer, format, width);
		}
#endif
		
		// DecimalFormat is a little disappointing coming from Fortran or C's printf.
		// Since it doesn't pad on the left, the elements will come out different
		// widths.  Consequently, we'll pass the desired column width in as an
		// argument and do the extra padding ourselves.
		
		/// <summary> Print the matrix to the output stream.  Line the elements up in columns.
		/// Use the format object, and right justify within columns of width
		/// characters.
		/// Note that is the matrix is to be read back in, you probably will want
		/// to use a NumberFormat that is set to US Locale.
		/// </summary>
		/// <param name="output">the output stream.
		/// </param>
		/// <param name="format">A formatting object to format the matrix elements 
		/// </param>
		/// <param name="width"> Column width.
		/// </param>
		/// <seealso cref="java.text.DecimalFormat.setDecimalFormatSymbols">
		/// </seealso>
		public virtual void  print(System.IO.StreamWriter output, TextNumberFormat format, int width)
		{
			//UPGRADE_TODO: Method 'java.io.PrintWriter.println' was converted to 'System.IO.TextWriter.WriteLine' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioPrintWriterprintln'"
			output.WriteLine(); // start on new line.
			for (int i = 0; i < m; i++)
			{
				for (int j = 0; j < n; j++)
				{
					System.String s = format.FormatDouble(A[i][j]); // format the number
					int padding = System.Math.Max(1, width - s.Length); // At _least_ 1 space
					for (int k = 0; k < padding; k++)
						output.Write(' ');
					output.Write(s);
				}
				//UPGRADE_TODO: Method 'java.io.PrintWriter.println' was converted to 'System.IO.TextWriter.WriteLine' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioPrintWriterprintln'"
				output.WriteLine();
			}
			//UPGRADE_TODO: Method 'java.io.PrintWriter.println' was converted to 'System.IO.TextWriter.WriteLine' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioPrintWriterprintln'"
			output.WriteLine(); // end with blank line.
		}
		
		/// <summary> Read a matrix from a stream.  The format is the same the print method,
		/// so printed matrices can be read back in (provided they were printed using
		/// US Locale).  XmlElements are separated by
		/// whitespace, all the elements for each row appear on a single line,
		/// the last row is followed by a blank line.
		/// <p/>
		/// Note: This format differs from the one that can be read via the
		/// Matrix(Reader) constructor! For that format, the write(Writer) method
		/// is used (from the original weka.core.Matrix class).
		/// 
		/// </summary>
		/// <param name="input">the input stream.
		/// </param>
		/// <seealso cref="Matrix(Reader)">
		/// </seealso>
		/// <seealso cref="write(Writer)">
		/// </seealso>
		public static Matrix read(System.IO.StreamReader input)
		{
			StreamTokenizer tokenizer = new StreamTokenizer(input);
			
			// Although StreamTokenizer will parse numbers, it doesn't recognize
			// scientific notation (E or D); however, Double.valueOf does.
			// The strategy here is to disable StreamTokenizer's number parsing.
			// We'll only get whitespace delimited words, EOL's and EOF's.
			// These words should all be numbers, for Double.valueOf to parse.

            tokenizer.Settings.SetDefaults();//.ResetSyntax();
			tokenizer.Settings.WordChars(0, 255);
			tokenizer.Settings.WhitespaceChars(0,(int) ' ');//  .WhitespaceChars(0, ' ');
			tokenizer.Settings.GrabEol=true;
			System.Collections.ArrayList v = System.Collections.ArrayList.Synchronized(new System.Collections.ArrayList(10));
			
			// Ignore initial empty lines
            Token token;
            tokenizer.NextToken(out token);
			while (token is EolToken)// == SupportClass.StreamTokenizerSupport.TT_EOL)
				;
			//if (token.ttype == SupportClass.StreamTokenizerSupport.TT_EOF)
            if (token is EofToken)
				throw new System.IO.IOException("Unexpected EOF on matrix read.");
            do
            {
               // v.Add(System.Double.Parse(tokenizer.sval)); // Read & store 1st row.
                v.Add(System.Double.Parse(token.StringValue)); // Read & store 1st row.
                tokenizer.NextToken(out token);
            }
            while (token is WordToken);
			//while (tokenizer.NextToken() == SupportClass.StreamTokenizerSupport.TT_WORD);
			
			int n = v.Count; // Now we've got the number of columns!
			double[] row = new double[n];
			for (int j = 0; j < n; j++)
			// extract the elements of the 1st row.
				row[j] = ((System.Double) v[j]);
			v.Clear();
			v.Add(row); // Start storing rows instead of columns.
            tokenizer.NextToken(out token);
            while (token is WordToken)
			//while (tokenizer.NextToken() == SupportClass.StreamTokenizerSupport.TT_WORD)
			{
				// While non-empty lines
				v.Add(row = new double[n]);
				int j = 0;
				do 
				{
					if (j >= n)
						throw new System.IO.IOException("Row " + v.Count + " is too long.");
					//row[j++] = System.Double.Parse(tokenizer.sval);
                    row[j++] = System.Double.Parse(token.StringValue);
                    tokenizer.NextToken(out token);
				}
                while (token is WordToken);
              
				//while (tokenizer.NextToken() == SupportClass.StreamTokenizerSupport.TT_WORD);
				if (j < n)
					throw new System.IO.IOException("Row " + v.Count + " is too short.");
			}
			int m = v.Count; // Now we've got the number of rows.
			double[][] A = new double[m][];
			v.CopyTo(A); // copy the rows out of the vector
			return new Matrix(A);
		}
		
		
		/// <summary> Check if size(A) == size(B) </summary>
		private void  checkMatrixDimensions(Matrix B)
		{
			if (B.m != m || B.n != n)
			{
				throw new System.ArgumentException("Matrix dimensions must agree.");
			}
		}
		
		/// <summary> Writes out a matrix. The format can be read via the Matrix(Reader)
		/// constructor.
		/// 
		/// </summary>
		/// <param name="w">the output Writer
		/// </param>
		/// <throws>     Exception if an error occurs </throws>
		/// <seealso cref="Matrix(Reader)">
		/// </seealso>
		/// <author>     FracPete, taken from old weka.core.Matrix class
		/// </author>
		//UPGRADE_ISSUE: Class hierarchy differences between 'java.io.Writer' and 'System.IO.StreamWriter' may cause compilation errors. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1186'"
		public virtual void  write(System.IO.StreamWriter w)
		{
			w.Write("% Rows\tColumns\n");
			w.Write("" + RowDimension + "\t" + ColumnDimension + "\n");
			w.Write("% Matrix elements\n");
			for (int i = 0; i < RowDimension; i++)
			{
				for (int j = 0; j < ColumnDimension; j++)
					w.Write("" + get_Renamed(i, j) + "\t");
				w.Write("\n");
			}
			w.Flush();
		}
		
		/// <summary> Converts a matrix to a string
		/// 
		/// </summary>
		/// <returns>    the converted string
		/// </returns>
		/// <author>     FracPete, taken from old weka.core.Matrix class
		/// </author>
		public override System.String ToString()
		{
			// Determine the width required for the maximum element,
			// and check for fractional display requirement.
			double maxval = 0;
			bool fractional = false;
			for (int i = 0; i < RowDimension; i++)
			{
				for (int j = 0; j < ColumnDimension; j++)
				{
					double current = get_Renamed(i, j);
					if (current < 0)
						current *= (- 11);
					if (current > maxval)
						maxval = current;
					double fract = System.Math.Abs(current - System.Math.Round((double) current));
					if (!fractional && ((System.Math.Log(fract) / System.Math.Log(10)) >= - 2))
					{
						fractional = true;
					}
				}
			}
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			int width = (int) (System.Math.Log(maxval) / System.Math.Log(10) + (fractional?4:1));
			
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			for (int i = 0; i < RowDimension; i++)
			{
				for (int j = 0; j < ColumnDimension; j++)
					text.Append(" ").Append(Utils.doubleToString(get_Renamed(i, j), width, (fractional?2:0)));
				text.Append("\n");
			}
			
			return text.ToString();
		}
		
		/// <summary> converts the Matrix into a single line Matlab string: matrix is enclosed 
		/// by parentheses, rows are separated by semicolon and single cells by
		/// blanks, e.g., [1 2; 3 4].
		/// </summary>
		/// <returns>      the matrix in Matlab single line format
		/// </returns>
		public virtual System.String toMatlab()
		{
			System.Text.StringBuilder result;
			int i;
			int n;
			
			result = new System.Text.StringBuilder();
			
			result.Append("[");
			
			for (i = 0; i < RowDimension; i++)
			{
				if (i > 0)
					result.Append("; ");
				
				for (n = 0; n < ColumnDimension; n++)
				{
					if (n > 0)
						result.Append(" ");
					result.Append(get_Renamed(i, n).ToString());
				}
			}
			
			result.Append("]");
			
			return result.ToString();
		}
		
		/// <summary> creates a matrix from the given Matlab string.</summary>
		/// <param name="matlab"> the matrix in matlab format
		/// </param>
		/// <returns>        the matrix represented by the given string
		/// </returns>
		/// <seealso cref="toMatlab()">
		/// </seealso>
		public static Matrix parseMatlab(System.String matlab)
		{
			Tokenizer tokRow;
			Tokenizer tokCol;
			int rows;
			int cols;
			Matrix result;
			System.String cells;
			
			// get content
			cells = matlab.Substring(matlab.IndexOf("[") + 1, (matlab.IndexOf("]")) - (matlab.IndexOf("[") + 1)).Trim();
			
			// determine dimenions
			tokRow = new Tokenizer(cells, ';');
			rows = tokRow.Count;
			tokCol = new Tokenizer(tokRow.NextToken(), ' ');
			cols = tokCol.Count;
			
			// fill matrix
			result = new Matrix(rows, cols);
			tokRow = new Tokenizer(cells, ';');
			rows = 0;
			while (tokRow.HasMoreTokens())
			{
				tokCol = new Tokenizer(tokRow.NextToken(), ' ');
				cols = 0;
				while (tokCol.HasMoreTokens())
				{
					result.set_Renamed(rows, cols, System.Double.Parse(tokCol.NextToken()));
					cols++;
				}
				rows++;
			}
			
			return result;
		}
		
		/// <summary> Main method for testing this class.</summary>
		//	public static void main(String[] args) 
		//	{
		//		Matrix        I;
		//		Matrix        A;
		//		Matrix        B;
		//
		//		try 
		//		{
		//			// Identity
		//			System.out.println("\nIdentity\n");
		//			I = Matrix.identity(3, 5);
		//			System.out.println("I(3,5)\n" + I);
		//      
		//			// basic operations - square
		//			System.out.println("\nbasic operations - square\n");
		//			A = Matrix.random(3, 3);
		//			B = Matrix.random(3, 3);
		//			System.out.println("A\n" + A);
		//			System.out.println("B\n" + B);
		//			System.out.println("A'\n" + A.inverse());
		//			System.out.println("A^T\n" + A.transpose());
		//			System.out.println("A+B\n" + A.plus(B));
		//			System.out.println("A*B\n" + A.times(B));
		//			System.out.println("X from A*X=B\n" + A.solve(B));
		//
		//			// basic operations - non square
		//			System.out.println("\nbasic operations - non square\n");
		//			A = Matrix.random(2, 3);
		//			B = Matrix.random(3, 4);
		//			System.out.println("A\n" + A);
		//			System.out.println("B\n" + B);
		//			System.out.println("A*B\n" + A.times(B));
		//
		//			// sqrt
		//			System.out.println("\nsqrt (1)\n");
		//			A = new Matrix(new double[][]{{5,-4,1,0,0},{-4,6,-4,1,0},{1,-4,6,-4,1},{0,1,-4,6,-4},{0,0,1,-4,5}});
		//			System.out.println("A\n" + A);
		//			System.out.println("sqrt(A)\n" + A.sqrt());
		//
		//			// sqrt
		//			System.out.println("\nsqrt (2)\n");
		//			A = new Matrix(new double[][]{{7, 10},{15, 22}});
		//			System.out.println("A\n" + A);
		//			System.out.println("sqrt(A)\n" + A.sqrt());
		//			System.out.println("det(A)\n" + A.det() + "\n");
		//
		//			// eigenvalue decomp.
		//			System.out.println("\nEigenvalue Decomposition\n");
		//			EigenvalueDecomposition evd = A.eig();
		//			System.out.println("[V,D] = eig(A)");
		//			System.out.println("- V\n" + evd.getV());
		//			System.out.println("- D\n" + evd.getD());
		//
		//			// LU decomp.
		//			System.out.println("\nLU Decomposition\n");
		//			LUDecomposition lud = A.lu();
		//			System.out.println("[L,U,P] = lu(A)");
		//			System.out.println("- L\n" + lud.getL());
		//			System.out.println("- U\n" + lud.getU());
		//			System.out.println("- P\n" + Utils.arrayToString(lud.getPivot()) + "\n");
		//
		//			// regression
		//			System.out.println("\nRegression\n");
		//			B = new Matrix(new double[][]{{3},{2}});
		//			double ridge = 0.5;
		//			double[] weights = new double[]{0.3, 0.7};
		//			LinearRegression lr = A.regression(B, ridge);
		//			System.out.println("A\n" + A);
		//			System.out.println("B\n" + B);
		//			System.out.println("ridge = " + ridge + "\n");
		//			System.out.println("weights = " + Utils.arrayToString(weights) + "\n");
		//			System.out.println("A.regression(B, ridge)\n" 
		//				+ A.regression(B, ridge) + "\n");
		//			System.out.println("A.regression(B, weights, ridge)\n" 
		//				+ A.regression(B, weights, ridge) + "\n");
		//
		//			// writer/reader
		//			System.out.println("\nWriter/Reader\n");
		//			StringWriter writer = new StringWriter();
		//			A.write(writer);
		//			System.out.println("A.write(Writer)\n" + writer);
		//			A = new Matrix(new StringReader(writer.toString()));
		//			System.out.println("A = new Matrix.read(Reader)\n" + A);
		//
		//			// Matlab
		//			System.out.println("\nMatlab-Format\n");
		//			String matlab = "[ 1   2;3 4 ]";
		//			System.out.println("Matlab: " + matlab);
		//			System.out.println("from Matlab:\n" + Matrix.parseMatlab(matlab));
		//			System.out.println("to Matlab:\n" + Matrix.parseMatlab(matlab).toMatlab());
		//			matlab = "[1 2 3 4;3 4 5 6;7 8 9 10]";
		//			System.out.println("Matlab: " + matlab);
		//			System.out.println("from Matlab:\n" + Matrix.parseMatlab(matlab));
		//			System.out.println("to Matlab:\n" + Matrix.parseMatlab(matlab).toMatlab() + "\n");
		//		}
		//		catch (Exception e) 
		//		{
		//			e.printStackTrace();
		//		}
		//	}
	}
}