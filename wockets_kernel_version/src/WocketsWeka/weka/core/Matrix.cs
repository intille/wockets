/*
*    Matrix.java
*    Copyright (C) 1999 Yong Wang, Eibe Frank, Len Trigg, Gabi Schmidberger
*
*/
using System;
namespace weka.core
{
	
	/// <summary> Class for performing operations on a matrix of floating-point values.
	/// <p/>
	/// Deprecated: Uses internally the code of the sub-package 
	/// <code>weka.core.matrix</code> - only for backwards compatibility.
	/// 
	/// </summary>
	/// <author>  Gabi Schmidberger (gabi@cs.waikato.ac.nz)
	/// </author>
	/// <author>  Yong Wang (yongwang@cs.waikato.ac.nz)
	/// </author>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <author>  Len Trigg (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <author>  Fracpete (fracpete at waikato dot ac dot nz)
	/// </author>
	/// <version>  $Revision: 1.18.2.2 $
	/// </version>
	/// <deprecated> Use instead <code>weka.core.matrix.Matrix</code> - only for
	/// backwards compatibility. 
	/// </deprecated>
#if !PocketPC
    [Serializable]
#endif
	public class Matrix : System.ICloneable
	{
		/// <summary> Returns true if the matrix is symmetric.
		/// 
		/// </summary>
		/// <returns> boolean true if matrix is symmetric.
		/// </returns>
		virtual public bool Symmetric
		{
			get
			{
				return m_Matrix.Symmetric;
			}
			
		}
		/// <summary> Returns the L part of the matrix.
		/// This does only make sense after LU decomposition.
		/// 
		/// </summary>
		/// <returns> matrix with the L part of the matrix; 
		/// </returns>
		/// <seealso cref="LUDecomposition()">
		/// </seealso>
		virtual public Matrix L
		{
			get
			{
				int nr = numRows(); // num of rows
				int nc = numColumns(); // num of columns
				double[][] ld = new double[nr][];
				for (int i = 0; i < nr; i++)
				{
					ld[i] = new double[nc];
				}
				
				for (int i = 0; i < nr; i++)
				{
					for (int j = 0; (j < i) && (j < nc); j++)
					{
						ld[i][j] = getXmlElement(i, j);
					}
					if (i < nc)
						ld[i][i] = 1;
				}
				Matrix l = new Matrix(ld);
				return l;
			}
			
		}
		/// <summary> Returns the U part of the matrix.
		/// This does only make sense after LU decomposition.
		/// 
		/// </summary>
		/// <returns> matrix with the U part of a matrix; 
		/// </returns>
		/// <seealso cref="LUDecomposition()">
		/// </seealso>
		virtual public Matrix U
		{
			get
			{
				int nr = numRows(); // num of rows
				int nc = numColumns(); // num of columns
				double[][] ud = new double[nr][];
				for (int i = 0; i < nr; i++)
				{
					ud[i] = new double[nc];
				}
				
				for (int i = 0; i < nr; i++)
				{
					for (int j = i; j < nc; j++)
					{
						ud[i][j] = getXmlElement(i, j);
					}
				}
				Matrix u = new Matrix(ud);
				return u;
			}
			
		}
		
		/// <summary> The actual matrix </summary>
		protected internal weka.core.matrix.Matrix m_Matrix = null;
		
		/// <summary> Constructs a matrix and initializes it with default values.
		/// 
		/// </summary>
		/// <param name="nr">the number of rows
		/// </param>
		/// <param name="nc">the number of columns
		/// </param>
		public Matrix(int nr, int nc)
		{
			m_Matrix = new weka.core.matrix.Matrix(nr, nc);
		}
		
		/// <summary> Constructs a matrix using a given array.
		/// 
		/// </summary>
		/// <param name="array">the values of the matrix
		/// </param>
		public Matrix(double[][] array)
		{
			m_Matrix = new weka.core.matrix.Matrix(array);
		}
		
		/// <summary> Reads a matrix from a reader. The first line in the file should
		/// contain the number of rows and columns. Subsequent lines
		/// contain elements of the matrix.
		/// 
		/// </summary>
		/// <param name="r">the reader containing the matrix
		/// </param>
		/// <throws>  Exception if an error occurs </throws>
		//UPGRADE_ISSUE: Class hierarchy differences between 'java.io.Reader' and 'System.IO.StreamReader' may cause compilation errors. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1186'"
		public Matrix(System.IO.StreamReader r)
		{
			m_Matrix = new weka.core.matrix.Matrix(r);
		}
		
		/// <summary> Creates and returns a clone of this object.
		/// 
		/// </summary>
		/// <returns> a clone of this instance.
		/// </returns>
		/// <throws>  Exception if an error occurs </throws>
		public virtual System.Object Clone()
		{
			try
			{
				return new Matrix(m_Matrix.ArrayCopy);
			}
			catch (System.Exception e)
			{
				return null;
			}
		}
		
		/// <summary> Writes out a matrix.
		/// 
		/// </summary>
		/// <param name="w">the output Writer
		/// </param>
		/// <throws>  Exception if an error occurs </throws>
		//UPGRADE_ISSUE: Class hierarchy differences between 'java.io.Writer' and 'System.IO.StreamWriter' may cause compilation errors. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1186'"
		public virtual void  write(System.IO.StreamWriter w)
		{
			m_Matrix.write(w);
		}
		
		/// <summary> returns the internal matrix</summary>
		/// <seealso cref="m_Matrix">
		/// </seealso>
		protected internal virtual weka.core.matrix.Matrix getMatrix()
		{
			return m_Matrix;
		}
		
		/// <summary> Returns the value of a cell in the matrix.
		/// 
		/// </summary>
		/// <param name="rowIndex">the row's index
		/// </param>
		/// <param name="columnIndex">the column's index
		/// </param>
		/// <returns> the value of the cell of the matrix
		/// </returns>
		public double getXmlElement(int rowIndex, int columnIndex)
		{
			return m_Matrix.get_Renamed(rowIndex, columnIndex);
		}
		
		/// <summary> Add a value to an element.
		/// 
		/// </summary>
		/// <param name="rowIndex">the row's index.
		/// </param>
		/// <param name="columnIndex">the column's index.
		/// </param>
		/// <param name="value">the value to add.
		/// </param>
		public void  addElement(int rowIndex, int columnIndex, double value_Renamed)
		{
			m_Matrix.set_Renamed(rowIndex, columnIndex, m_Matrix.get_Renamed(rowIndex, columnIndex) + value_Renamed);
		}
		
		/// <summary> Returns the number of rows in the matrix.
		/// 
		/// </summary>
		/// <returns> the number of rows
		/// </returns>
		public int numRows()
		{
			return m_Matrix.RowDimension;
		}
		
		/// <summary> Returns the number of columns in the matrix.
		/// 
		/// </summary>
		/// <returns> the number of columns
		/// </returns>
		public int numColumns()
		{
			return m_Matrix.ColumnDimension;
		}
		
		/// <summary> Sets an element of the matrix to the given value.
		/// 
		/// </summary>
		/// <param name="rowIndex">the row's index
		/// </param>
		/// <param name="columnIndex">the column's index
		/// </param>
		/// <param name="value">the value
		/// </param>
		public void  setXmlElement(int rowIndex, int columnIndex, double value_Renamed)
		{
			m_Matrix.set_Renamed(rowIndex, columnIndex, value_Renamed);
		}
		
		/// <summary> Sets a row of the matrix to the given row. Performs a deep copy.
		/// 
		/// </summary>
		/// <param name="index">the row's index
		/// </param>
		/// <param name="newRow">an array of doubles
		/// </param>
		public void  setRow(int index, double[] newRow)
		{
			for (int i = 0; i < newRow.Length; i++)
				m_Matrix.set_Renamed(index, i, newRow[i]);
		}
		
		/// <summary> Gets a row of the matrix and returns it as double array.
		/// 
		/// </summary>
		/// <param name="index">the row's index
		/// </param>
		/// <returns> an array of doubles
		/// </returns>
		public virtual double[] getRow(int index)
		{
			double[] newRow = new double[this.numColumns()];
			for (int i = 0; i < newRow.Length; i++)
				newRow[i] = getXmlElement(index, i);
			
			return newRow;
		}
		
		/// <summary> Gets a column of the matrix and returns it as a double array.
		/// 
		/// </summary>
		/// <param name="index">the column's index
		/// </param>
		/// <returns> an array of doubles
		/// </returns>
		public virtual double[] getColumn(int index)
		{
			double[] newColumn = new double[this.numRows()];
			for (int i = 0; i < newColumn.Length; i++)
				newColumn[i] = getXmlElement(i, index);
			
			return newColumn;
		}
		
		/// <summary> Sets a column of the matrix to the given column. Performs a deep copy.
		/// 
		/// </summary>
		/// <param name="index">the column's index
		/// </param>
		/// <param name="newColumn">an array of doubles
		/// </param>
		public void  setColumn(int index, double[] newColumn)
		{
			for (int i = 0; i < numRows(); i++)
				m_Matrix.set_Renamed(i, index, newColumn[i]);
		}
		
		/// <summary> Converts a matrix to a string
		/// 
		/// </summary>
		/// <returns> the converted string
		/// </returns>
		public override System.String ToString()
		{
			return m_Matrix.ToString();
		}
		
		/// <summary> Returns the sum of this matrix with another.
		/// 
		/// </summary>
		/// <returns> a matrix containing the sum.
		/// </returns>
		public Matrix add(Matrix other)
		{
			try
			{
				return new Matrix(m_Matrix.plus(other.getMatrix()).ArrayCopy);
			}
			catch (System.Exception e)
			{

				return null;
			}
		}
		
		/// <summary> Returns the transpose of a matrix.
		/// 
		/// </summary>
		/// <returns> the transposition of this instance.
		/// </returns>
		public Matrix transpose()
		{
			try
			{
				return new Matrix(m_Matrix.transpose().ArrayCopy);
			}
			catch (System.Exception e)
			{
				return null;
			}
		}
		
		/// <summary> Returns the multiplication of two matrices
		/// 
		/// </summary>
		/// <param name="b">the multiplication matrix
		/// </param>
		/// <returns> the product matrix
		/// </returns>
		public Matrix multiply(Matrix b)
		{
			try
			{
				return new Matrix(getMatrix().times(b.getMatrix()).ArrayCopy);
			}
			catch (System.Exception e)
			{
				return null;
			}
		}
		
		/// <summary> Performs a (ridged) linear regression.
		/// 
		/// </summary>
		/// <param name="y">the dependent variable vector
		/// </param>
		/// <param name="ridge">the ridge parameter
		/// </param>
		/// <returns> the coefficients 
		/// </returns>
		/// <throws>  IllegalArgumentException if not successful </throws>
		public double[] regression(Matrix y, double ridge)
		{
			return getMatrix().regression(y.getMatrix(), ridge).Coefficients;
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
		/// <returns> the coefficients 
		/// </returns>
		/// <throws>  IllegalArgumentException if the wrong number of weights were </throws>
		/// <summary> provided.
		/// </summary>
		public double[] regression(Matrix y, double[] w, double ridge)
		{
			return getMatrix().regression(y.getMatrix(), w, ridge).Coefficients;
		}
		
		/// <summary> Performs a LUDecomposition on the matrix.
		/// It changes the matrix into its LU decomposition.
		/// 
		/// </summary>
		/// <returns> the indices of the row permutation
		/// </returns>
		public virtual int[] LUDecomposition()
		{
			// decompose
			weka.core.matrix.LUDecomposition lu = m_Matrix.lu();
			
			// singular? old class throws Exception!
			if (!lu.Nonsingular)
				throw new System.Exception("Matrix is singular");
			
			weka.core.matrix.Matrix u = lu.U;
			weka.core.matrix.Matrix l = lu.L;
			
			// modify internal matrix
			int nr = numRows();
			int nc = numColumns();
			for (int i = 0; i < nr; i++)
			{
				for (int j = 0; j < nc; j++)
				{
					if (j < i)
						setXmlElement(i, j, l.get_Renamed(i, j));
					else
						setXmlElement(i, j, u.get_Renamed(i, j));
				}
			}
			
			u = null;
			l = null;
			
			return lu.Pivot;
		}
		
		/// <summary> Solve A*X = B using backward substitution.
		/// A is current object (this). Note that this matrix will be changed! 
		/// B parameter bb.
		/// X returned in parameter bb.
		/// 
		/// </summary>
		/// <param name="bb">first vector B in above equation then X in same equation.
		/// </param>
		public virtual void  solve(double[] bb)
		{
			// solve
			weka.core.matrix.Matrix x = m_Matrix.solve(new weka.core.matrix.Matrix(bb, bb.Length));
			
			// move X into bb
			int nr = x.RowDimension;
			for (int i = 0; i < nr; i++)
				bb[i] = x.get_Renamed(i, 0);
		}
		
		/// <summary> Performs Eigenvalue Decomposition using Householder QR Factorization
		/// 
		/// Matrix must be symmetrical.
		/// Eigenvectors are return in parameter V, as columns of the 2D array.
		/// (Real parts of) Eigenvalues are returned in parameter d.
		/// 
		/// </summary>
		/// <param name="V">double array in which the eigenvectors are returned 
		/// </param>
		/// <param name="d">array in which the eigenvalues are returned
		/// </param>
		/// <throws>  Exception if matrix is not symmetric </throws>
		public virtual void  eigenvalueDecomposition(double[][] V, double[] d)
		{
			
			// old class only worked with symmetric matrices!
			if (!this.Symmetric)
				throw new System.Exception("EigenvalueDecomposition: Matrix must be symmetric.");
			
			// perform eigenvalue decomposition
			weka.core.matrix.EigenvalueDecomposition eig = m_Matrix.eig();
			weka.core.matrix.Matrix v = eig.getV();
			double[] d2 = eig.RealEigenvalues;
			
			// transfer data
			int nr = numRows();
			int nc = numColumns();
			for (int i = 0; i < nr; i++)
				for (int j = 0; j < nc; j++)
					V[i][j] = v.get_Renamed(i, j);
			
			for (int i = 0; i < d2.Length; i++)
				d[i] = d2[i];
		}
		
		/// <summary> Returns sqrt(a^2 + b^2) without under/overflow.
		/// 
		/// </summary>
		/// <param name="a">length of one side of rectangular triangle
		/// </param>
		/// <param name="b">length of other side of rectangular triangle
		/// </param>
		/// <returns> lenght of third side
		/// </returns>
		protected internal static double hypot(double a, double b)
		{
			return weka.core.matrix.Maths.hypot(a, b);
		}
		
		/// <summary> converts the Matrix into a single line Matlab string: matrix is enclosed 
		/// by parentheses, rows are separated by semicolon and single cells by
		/// blanks, e.g., [1 2; 3 4].
		/// </summary>
		/// <returns>      the matrix in Matlab single line format
		/// </returns>
		public virtual System.String toMatlab()
		{
			return getMatrix().toMatlab();
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
			return new Matrix(weka.core.matrix.Matrix.parseMatlab(matlab).Array);
		}
		
		/// <summary> Main method for testing this class.</summary>
		//	public static void main(String[] ops) 
		//	{
		//		double[] first = {2.3, 1.2, 5};
		//		double[] second = {5.2, 1.4, 9};
		//		double[] response = {4, 7, 8};
		//		double[] weights = {1, 2, 3};
		//
		//		try 
		//		{
		//			// test eigenvaluedecomposition
		//			double[][] m = {{1, 2, 3}, {2, 5, 6},{3, 6, 9}};
		//			Matrix M = new Matrix(m);
		//			int n = M.numRows();
		//			double[][] V = new double[n][n];
		//			double[] d = new double[n];
		//			double[] e = new double[n];
		//			M.eigenvalueDecomposition(V, d);
		//			Matrix v = new Matrix(V);
		//			// M.testEigen(v, d, );
		//			// end of test-eigenvaluedecomposition
		//      
		//			Matrix a = new Matrix(2, 3);
		//			Matrix b = new Matrix(3, 2);
		//			System.out.println("Number of columns for a: " + a.numColumns());
		//			System.out.println("Number of rows for a: " + a.numRows());
		//			a.setRow(0, first);
		//			a.setRow(1, second);
		//			b.setColumn(0, first);
		//			b.setColumn(1, second);
		//			System.out.println("a:\n " + a);
		//			System.out.println("b:\n " + b);
		//			System.out.println("a (0, 0): " + a.getXmlElement(0, 0));
		//			System.out.println("a transposed:\n " + a.transpose());
		//			System.out.println("a * b:\n " + a.multiply(b));
		//			Matrix r = new Matrix(3, 1);
		//			r.setColumn(0, response);
		//			System.out.println("r:\n " + r);
		//			System.out.println("Coefficients of regression of b on r: ");
		//			double[] coefficients = b.regression(r, 1.0e-8);
		//			for (int i = 0; i < coefficients.length; i++) 
		//			{
		//				System.out.print(coefficients[i] + " ");
		//			}
		//			System.out.println();
		//			System.out.println("Weights: ");
		//			for (int i = 0; i < weights.length; i++) 
		//			{
		//				System.out.print(weights[i] + " ");
		//			}
		//			System.out.println();
		//			System.out.println("Coefficients of weighted regression of b on r: ");
		//			coefficients = b.regression(r, weights, 1.0e-8);
		//			for (int i = 0; i < coefficients.length; i++) 
		//			{
		//				System.out.print(coefficients[i] + " ");
		//			}
		//			System.out.println();
		//			a.setXmlElement(0, 0, 6);
		//			System.out.println("a with (0, 0) set to 6:\n " + a);
		//			a.write(new java.io.FileWriter("main.matrix"));
		//			System.out.println("wrote matrix to \"main.matrix\"\n" + a);
		//			a = new Matrix(new java.io.FileReader("main.matrix"));
		//			System.out.println("read matrix from \"main.matrix\"\n" + a);
		//		} 
		//		catch (Exception e) 
		//		{
		//			e.printStackTrace();
		//		}
		//	}
	}
}