using System;
using System.Collections.Generic;
using System.Text;

namespace WocketsWeka.Utils
{
    public class CubicSpline
    {

        private int nPoints = 0; // no. of tabulated points
        private double[] y = null; // y=f(x) tabulated function
        private double[] x = null; // x in tabulated function f(x)
        private double[] d2ydx2 = null; // second derivatives of y
        private double yp1 = System.Double.NaN; // first derivative at point one
        // default value = NaN (natural spline)
        private double ypn = System.Double.NaN; // first derivative at point n
        // default value = NaN (natural spline)
        private bool derivCalculated = false; // = true when the derivatives have been calculated

        // Constructors
        // Constructor with data arrays initialised to arrays x and y
        public CubicSpline(double[] x, double[] y)
        {

            this.nPoints = x.Length;

            if (this.nPoints != y.Length)
                throw new System.ArgumentException("Arrays x and y are of different length" + this.nPoints + " " + y.Length);
            if (this.nPoints < 3)
                throw new System.ArgumentException("A minimum of three data points is needed");

            this.x = x;
            this.y = y;

            this.d2ydx2 = new double[nPoints];
        }

        // Constructor with data arrays initialised to zero
        // Primarily for use by BiCubicSpline
        public CubicSpline(int nPoints)
        {
            this.nPoints = nPoints;
            if (this.nPoints < 3)
                throw new System.ArgumentException("A minimum of three data points is needed");
            this.x = new double[nPoints];
            this.y = new double[nPoints];
            this.d2ydx2 = new double[nPoints];
        }

        //  METHODS
        // Resets the x y data arrays - primarily for use in BiCubicSpline
        public virtual void resetData(double[] x, double[] y)
        {
            if (x.Length != y.Length)
                throw new System.ArgumentException("Arrays x and y are of different length");
            if (this.nPoints != x.Length)
                throw new System.ArgumentException("Original array length not matched by new array length");
            for (int i = 0; i < this.nPoints; i++)
            {
                this.x[i] = x[i];
                this.y[i] = y[i];
            }
        }

        // Returns a new CubicSpline setting array lengths to n and all array values to zero with natural spline default
        // Primarily for use in BiCubicSpline
        public virtual CubicSpline zero(int n)
        {
            if (n < 3)
                throw new System.ArgumentException("A minimum of three data points is needed");
            CubicSpline aa = new CubicSpline(n);
            return aa;
        }

        // Create a one dimensional array of cubic spline objects of length n each of array length m
        // Primarily for use in BiCubicSpline
        public virtual CubicSpline[] oneDarray(int n, int m)
        {
            if (m < 3)
                throw new System.ArgumentException("A minimum of three data points is needed");
            CubicSpline[] a = new CubicSpline[n];
            for (int i = 0; i < n; i++)
            {
                a[i] = zero(m);
            }
            return a;
        }

        // Enters the first derivatives of the cubic spline at
        // the first and last point of the tabulated data
        // Overrides a natural spline
        public virtual void setDerivLimits(double yp1, double ypn)
        {
            this.yp1 = yp1;
            this.ypn = ypn;
        }

        // Resets a natural spline
        // Use above - this kept for backward compatibility
        public virtual void setDerivLimits()
        {
            this.yp1 = System.Double.NaN;
            this.ypn = System.Double.NaN;
        }

        // Enters the first derivatives of the cubic spline at
        // the first and last point of the tabulated data
        // Overrides a natural spline
        // Use setDerivLimits(double yp1, double ypn) - this kept for backward compatibility
        public virtual void setDeriv(double yp1, double ypn)
        {
            this.yp1 = yp1;
            this.ypn = ypn;
        }

        // Returns the internal array of second derivatives
        public virtual double[] getDeriv()
        {
            if (!this.derivCalculated)
                this.calcDeriv();
            return this.d2ydx2;
        }

        // Sets the internal array of second derivatives
        // Used primarily with BiCubicSpline
        public virtual void setDeriv(double[] deriv)
        {
            this.d2ydx2 = deriv;
            this.derivCalculated = true;
        }

        //  Calculates the second derivatives of the tabulated function
        //  for use by the cubic spline interpolation method (.interpolate)
        //  This method follows the procedure in Numerical Methods C language procedure for calculating second derivatives
        public virtual void calcDeriv()
        {
            double p = 0.0D, qn = 0.0D, sig = 0.0D, un = 0.0D;
            double[] u = new double[nPoints];

            if (this.yp1 != this.yp1)
            {
                d2ydx2[0] = u[0] = 0.0;
            }
            else
            {
                this.d2ydx2[0] = -0.5;
                u[0] = (3.0 / (this.x[1] - this.x[0])) * ((this.y[1] - this.y[0]) / (this.x[1] - this.x[0]) - this.yp1);
            }

            for (int i = 1; i <= this.nPoints - 2; i++)
            {
                sig = (this.x[i] - this.x[i - 1]) / (this.x[i + 1] - this.x[i - 1]);
                p = sig * this.d2ydx2[i - 1] + 2.0;
                this.d2ydx2[i] = (sig - 1.0) / p;
                u[i] = (this.y[i + 1] - this.y[i]) / (this.x[i + 1] - this.x[i]) - (this.y[i] - this.y[i - 1]) / (this.x[i] - this.x[i - 1]);
                u[i] = (6.0 * u[i] / (this.x[i + 1] - this.x[i - 1]) - sig * u[i - 1]) / p;
            }

            if (this.ypn != this.ypn)
            {
                qn = un = 0.0;
            }
            else
            {
                qn = 0.5;
                un = (3.0 / (this.x[nPoints - 1] - this.x[this.nPoints - 2])) * (this.ypn - (this.y[this.nPoints - 1] - this.y[this.nPoints - 2]) / (this.x[this.nPoints - 1] - x[this.nPoints - 2]));
            }

            this.d2ydx2[this.nPoints - 1] = (un - qn * u[this.nPoints - 2]) / (qn * this.d2ydx2[this.nPoints - 2] + 1.0);
            for (int k = this.nPoints - 2; k >= 0; k--)
            {
                this.d2ydx2[k] = this.d2ydx2[k] * this.d2ydx2[k + 1] + u[k];
            }
            this.derivCalculated = true;
        }

        //  INTERPOLATE
        //  Returns an interpolated value of y for a value of x from a tabulated function y=f(x)
        //  after the data has been entered via a constructor.
        //  The derivatives are calculated, bt calcDeriv(), on the first call to this method ands are
        //  then stored for use on all subsequent calls
        public virtual double interpolate(double xx)
        {

            if (xx < this.x[0] || xx > this.x[this.nPoints - 1])
            {
                //commented this (EMT) so tha values at begining and end of signal can be interpolated
                //    throw new IllegalArgumentException("x ("+xx+") is outside the range of data points ("+x[0]+" to "+x[this.nPoints-1]);
            }

            if (!this.derivCalculated)
                this.calcDeriv();

            double h = 0.0D, b = 0.0D, a = 0.0D, yy = 0.0D;
            int k = 0;
            int klo = 0;
            int khi = this.nPoints - 1;
            while (khi - klo > 1)
            {
                k = (khi + klo) >> 1;
                if (this.x[k] > xx)
                {
                    khi = k;
                }
                else
                {
                    klo = k;
                }
            }
            h = this.x[khi] - this.x[klo];

            if (h == 0.0)
            {
                throw new System.ArgumentException("Two values of x are identical: point " + klo + " (" + this.x[klo] + ") and point " + khi + " (" + this.x[khi] + ")");
            }
            else
            {
                a = (this.x[khi] - xx) / h;
                b = (xx - this.x[klo]) / h;
                yy = a * this.y[klo] + b * this.y[khi] + ((a * a * a - a) * this.d2ydx2[klo] + (b * b * b - b) * this.d2ydx2[khi]) * (h * h) / 6.0;
            }
            return yy;
        }

        //  Returns an interpolated value of y for a value of x (xx) from a tabulated function y=f(x)
        //  after the derivatives (deriv) have been calculated independently of calcDeriv().
        public virtual double interpolate(double xx, double[] x, double[] y, double[] deriv)
        {
            if (((x.Length != y.Length) || (x.Length != deriv.Length)) || (y.Length != deriv.Length))
            {
                throw new System.ArgumentException("array lengths are not all equal");
            }
            int n = x.Length;
            double h = 0.0D, b = 0.0D, a = 0.0D, yy = 0.0D;

            int k = 0;
            int klo = 0;
            int khi = n - 1;
            while (khi - klo > 1)
            {
                k = (khi + klo) >> 1;
                if (x[k] > xx)
                {
                    khi = k;
                }
                else
                {
                    klo = k;
                }
            }
            h = x[khi] - x[klo];

            if (h == 0.0)
            {
                throw new System.ArgumentException("Two values of x are identical");
            }
            else
            {
                a = (x[khi] - xx) / h;
                b = (xx - x[klo]) / h;
                yy = a * y[klo] + b * y[khi] + ((a * a * a - a) * deriv[klo] + (b * b * b - b) * deriv[khi]) * (h * h) / 6.0;
            }
            return yy;
        }
    }
}
