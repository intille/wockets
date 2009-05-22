/*
*    NoSplit.java
*    Copyright (C) 1999 Eibe Frank
*
*/
using System;
using weka.core;
using WocketsWeka;
using System.Xml;
using System.IO;
namespace weka.classifiers.trees.j48
{
	
	/// <summary> Class implementing a "no-split"-split.
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.6 $
	/// </version>
    /// 
#if !PocketPC
    [Serializable()]  
#endif
	public sealed class NoSplit:ClassifierSplitModel
	{



        public override void toXML(TextWriter tw)
        {
            tw.WriteLine("<" + Constants.NOSPLIT_ELEMENT + " " + Constants.NUM_SUBSETS_ATTRIBUTE+ "=\"" + this.m_numSubsets + "\">");
            this.m_distribution.toXML(tw);
            tw.WriteLine("</" + Constants.NOSPLIT_ELEMENT + ">");            

        }

        public NoSplit(XmlNode split)
        {
            foreach (XmlAttribute xAttribute in split.Attributes)
            {
                if (xAttribute.Name == Constants.NUM_SUBSETS_ATTRIBUTE)
                    this.m_numSubsets= Convert.ToInt32(xAttribute.Value);
            }
            foreach (XmlNode iNode in split.ChildNodes)
            {
                if (iNode.Name == Constants.DISTRIBUTION)
                    this.m_distribution = new Distribution(iNode);                    
            }
        }
		/// <summary> Creates "no-split"-split for given distribution.</summary>
		public NoSplit(Distribution distribution)
		{
			
			m_distribution = new Distribution(distribution);
			m_numSubsets = 1;
		}
		
		/// <summary> Creates a "no-split"-split for a given set of instances.
		/// 
		/// </summary>
		/// <exception cref="Exception">if split can't be built successfully
		/// </exception>
		public override void  buildClassifier(Instances instances)
		{
			
			m_distribution = new Distribution(instances);
			m_numSubsets = 1;
		}
		
		/// <summary> Always returns 0 because only there is only one subset.</summary>
		public override int whichSubset(Instance instance)
		{
			
			return 0;
		}
		
		/// <summary> Always returns null because there is only one subset.</summary>
		public override double[] GetWeights(Instance instance)
		{
			
			return null;
		}
		
		/// <summary> Does nothing because no condition has to be satisfied.</summary>
		public override System.String leftSide(Instances instances)
		{
			
			return "";
		}
		
		/// <summary> Does nothing because no condition has to be satisfied.</summary>
		public override System.String rightSide(int index, Instances instances)
		{
			
			return "";
		}
		
		/// <summary> Returns a string containing java source code equivalent to the test
		/// made at this node. The instance being tested is called "i".
		/// 
		/// </summary>
		/// <param name="index">index of the nominal value tested
		/// </param>
		/// <param name="data">the data containing instance structure info
		/// </param>
		/// <returns> a value of type 'String'
		/// </returns>
		public override System.String sourceExpression(int index, Instances data)
		{
			
			return "true"; // or should this be false??
		}
		//UPGRADE_TODO: The following method was automatically generated and it must be implemented in order to preserve the class logic. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1232'"
		override public System.Object Clone()
		{
			return null;
		}
	}
}