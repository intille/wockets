/*    J48.java
*    Copyright (C) 1999 Eibe Frank
*/
using System;
using weka.classifiers.trees.j48;
using weka.core;
using weka.classifiers;
using weka.support;
using System.IO;
using WocketsWeka;
using System.Xml;
#if !PocketPC
using System.Runtime.Serialization.Formatters.Binary; 
#endif
namespace weka.classifiers.trees
{
	
	/// <summary> Class for generating an unpruned or a pruned C4.5 decision tree.
	/// For more information, see<p>
	/// 
	/// Ross Quinlan (1993). <i>C4.5: Programs for Machine Learning</i>, 
	/// Morgan Kaufmann Publishers, San Mateo, CA. </p>
	/// 
	/// Valid options are: <p>
	/// 
	/// -U <br>
	/// Use unpruned tree.<p>
	/// 
	/// -C confidence <br>
	/// Set confidence threshold for pruning. (Default: 0.25) <p>
	/// 
	/// -M number <br>
	/// Set minimum number of instances per leaf. (Default: 2) <p>
	/// 
	/// -R <br>
	/// Use reduced error pruning. No subtree raising is performed. <p>
	/// 
	/// -N number <br>
	/// Set number of folds for reduced error pruning. One fold is
	/// used as the pruning set. (Default: 3) <p>
	/// 
	/// -B <br>
	/// Use binary splits for nominal attributes. <p>
	/// 
	/// -S <br>
	/// Don't perform subtree raising. <p>
	/// 
	/// -L <br>
	/// Do not clean up after the tree has been built. <p>
	/// 
	/// -A <br>
	/// If set, Laplace smoothing is used for predicted probabilites. <p>
	/// 
	/// -Q <br>
	/// The seed for reduced-error pruning. <p>
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.2 $
	/// </version>
	/// <attribute>  System.ComponentModel.DescriptionAttribute("Class for generating an unpruned or a pruned C4.5 decision tree. For more information, see Ross Quinlan (1993). 'C4.5: Programs for Machine Learning', Morgan Kaufmann Publishers, San Mateo, CA. ")  </attribute>

    #if !PocketPC
    [Serializable()]  
    #endif
	public class J48:Classifier, Drawable, Matchable, Sourcable, WeightedInstancesHandler, Summarizable, AdditionalMeasureProducer, ITree
	{
		//code of alain
		public virtual Node FirstNode()
		{
			return m_root.FirstNode();
		}
		public virtual System.String DescriptionTree()
		{
			System.String _desc = m_unpruned?"J48 unpruned tree":"J48 pruned tree";
			return _desc + m_root.DescriptionTree();
		}
		//end of code
		
		// To maintain the same version number after adding m_ClassAttribute
		internal const long serialVersionUID = - 217733168393644444L;
		/// <summary>The decision tree </summary>
		private ClassifierTree m_root;
		/// <summary>Unpruned tree? </summary>
		private bool m_unpruned = false;
		/// <summary>Confidence level </summary>
		private float m_CF = 0.25f;
		/// <summary>Minimum number of instances </summary>
		private int m_minNumObj = 2;
		/// <summary>Determines whether probabilities are smoothed using
		/// Laplace correction when predictions are generated 
		/// </summary>
		private bool m_useLaplace = false;
		/// <summary>Use reduced error pruning? </summary>
		private bool m_reducedErrorPruning = false;
		/// <summary>Number of folds for reduced error pruning. </summary>
		private int m_numFolds = 3;
		/// <summary>Binary splits on nominal attributes? </summary>
		private bool m_binarySplits = false;
		/// <summary>Subtree raising to be performed? </summary>
		private bool m_subtreeRaising = true;
		/// <summary>Cleanup after the tree has been built. </summary>
		private bool m_noCleanup = false;
		/// <summary>Random number seed for reduced-error pruning. </summary>
		private int m_Seed = 1;



        public override void toXML(TextWriter tw)
        {
            tw.WriteLine("<" + Constants.DECISION_TREE_ELEMENT + " " +
                Constants.SERIAL_VERSION_ATTRIBUTE + "=\"" + serialVersionUID + "\"  " +
                Constants.PRUNED_ATTRIBUTE+ "=\"" + this.m_unpruned + "\"   "+
                Constants.CONFIDENCE_ATTRIBUTE + "=\"" + this.m_CF + "\"   " +
                Constants.MIN_NUM_OBJECTS_ATTRIBUTE + "=\"" + this.m_minNumObj + "\"   " +
                Constants.USE_LAPLACE_ATTRIBUTE + "=\"" + this.m_useLaplace + "\"   " +
                Constants.REDUCED_ERROR_PRUNING_ATTRIBUTE + "=\"" + this.m_reducedErrorPruning + "\"   " +
                Constants.NUM_FOLDS_ATTRIBUTE + "=\"" + this.m_numFolds + "\"   " +
                Constants.BINARY_SPLITS_ATTRIBUTE + "=\"" + this.m_binarySplits + "\"   " +
                Constants.SUBTREE_RAISING_ATTRIBUTE + "=\"" + this.m_subtreeRaising + "\"   " +
                Constants.NO_CLEANUP_ATTRIBUTE + "=\"" + this.m_noCleanup + "\"   " +
                Constants.SEED_ATTRIBUTE+ "=\"" + this.m_Seed + "\"   " +
                " xmlns=\"urn:mites-schema\">\n");
            m_root.toXML(tw);
          tw.WriteLine("</" + Constants.DECISION_TREE_ELEMENT + ">\n");
           
        }

        public override void buildClassifier(string fileName, Instances instances)
        {

            XmlDocument dom = new XmlDocument();
            dom.Load(fileName);
            XmlNode xNode = dom.DocumentElement;

            if ((xNode.Name == Constants.DECISION_TREE_ELEMENT) && (xNode.HasChildNodes))
            {

                foreach (XmlAttribute xAttribute in xNode.Attributes)
                {
                    if (xAttribute.Name == Constants.PRUNED_ATTRIBUTE)
                    {
                        if (xAttribute.Value == "True")
                            this.m_unpruned = true;
                        else
                            this.m_unpruned = false;
                    }
                    else if (xAttribute.Name == Constants.CONFIDENCE_ATTRIBUTE)                    
                        this.m_CF = (float) Convert.ToDouble(xAttribute.Value);
                    else if (xAttribute.Name == Constants.MIN_NUM_OBJECTS_ATTRIBUTE)
                        this.m_minNumObj = Convert.ToInt32(xAttribute.Value);
                    else if (xAttribute.Name == Constants.USE_LAPLACE_ATTRIBUTE)
                    {
                        if (xAttribute.Value == "True")
                            this.m_useLaplace = true;
                        else
                            this.m_useLaplace = false;     
                    }
                    else if (xAttribute.Name == Constants.REDUCED_ERROR_PRUNING_ATTRIBUTE)
                    {
                        if (xAttribute.Value == "True")
                            this.m_reducedErrorPruning = true;
                        else
                            this.m_reducedErrorPruning = false;        
                    }
                    else if (xAttribute.Name == Constants.NUM_FOLDS_ATTRIBUTE)
                        this.m_numFolds = Convert.ToInt32(xAttribute.Value);
                    else if (xAttribute.Name == Constants.BINARY_SPLITS_ATTRIBUTE)
                    {
                        if (xAttribute.Value == "True")
                            this.m_binarySplits = true;
                        else
                            this.m_binarySplits = false;  
                    }
                    else if (xAttribute.Name == Constants.SUBTREE_RAISING_ATTRIBUTE)
                    {
                        if (xAttribute.Value == "True")
                            this.m_subtreeRaising = true;
                        else
                            this.m_subtreeRaising = false;
                    }
                    else if (xAttribute.Name == Constants.NO_CLEANUP_ATTRIBUTE)
                    {
                        if (xAttribute.Value == "True")
                            this.m_noCleanup = true;
                        else
                            this.m_noCleanup = false;
                    }
                    else if (xAttribute.Name == Constants.SEED_ATTRIBUTE)
                        this.m_Seed = Convert.ToInt32(xAttribute.Value);                    
                }

                //Going through the subtrees
                foreach (XmlNode iNode in xNode.ChildNodes)
                {
                    if (iNode.Name == Constants.C45_PRUNEABLE_ELEMENT)
                    {
                        this.m_root = new C45PruneableClassifierTree(iNode, instances);
                    }
                }
            }
        }
		/// <summary> Generates the classifier.
		/// 
		/// </summary>
		/// <exception cref="Exception">if classifier can't be built successfully
		/// </exception>
		public override void  buildClassifier(Instances instances)
		{
			
			ModelSelection modSelection;
			
			if (m_binarySplits)
				modSelection = new BinC45ModelSelection(m_minNumObj, instances);
			else
				modSelection = new C45ModelSelection(m_minNumObj, instances);
			if (!m_reducedErrorPruning)
				m_root = new C45PruneableClassifierTree(modSelection, !m_unpruned, m_CF, m_subtreeRaising, !m_noCleanup);
			else
				m_root = new PruneableClassifierTree(modSelection, !m_unpruned, m_numFolds, !m_noCleanup, m_Seed);
			m_root.buildClassifier(instances);
			if (m_binarySplits)
			{
				((BinC45ModelSelection) modSelection).cleanup();
			}
			else
			{
				((C45ModelSelection) modSelection).cleanup();
			}
		}
		
		/// <summary> Classifies an instance.
		/// 
		/// </summary>
		/// <exception cref="Exception">if instance can't be classified successfully
		/// </exception>
		public override double classifyInstance(Instance instance)
		{
			
			return m_root.classifyInstance(instance);
		}
		
		/// <summary> Returns class probabilities for an instance.
		/// 
		/// </summary>
		/// <exception cref="Exception">if distribution can't be computed successfully
		/// </exception>
		public override double[] distributionForInstance(Instance instance)
		{
			
			return m_root.distributionForInstance(instance, m_useLaplace);
		}
		
		/// <summary>  Returns the type of graph this classifier
		/// represents.
		/// </summary>
		/// <returns> Drawable.TREE
		/// </returns>
		public virtual int graphType()
		{
			return weka.core.Drawable_Fields.TREE;
		}
		
		/// <summary> Returns graph describing the tree.
		/// 
		/// </summary>
		/// <exception cref="Exception">if graph can't be computed
		/// </exception>
		public virtual System.String graph()
		{
			
			return m_root.graph();
		}
		
		/// <summary> Returns tree in prefix order.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public virtual System.String prefix()
		{
			
			return m_root.prefix();
		}
		
		
		/// <summary> Returns tree as an if-then statement.
		/// 
		/// </summary>
		/// <returns> the tree as a Java if-then type statement
		/// </returns>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public virtual System.String toSource(System.String className)
		{
			
			System.Text.StringBuilder[] source = m_root.toSource(className);
			return "class " + className + " {\n\n" + "  public static double classify(Object [] i)\n" + "    throws Exception {\n\n" + "    double p = Double.NaN;\n" + source[0] + "    return p;\n" + "  }\n" + source[1] + "}\n";
		}
		
		
		
		/// <summary> Get the value of Seed.
		/// 
		/// </summary>
		/// <returns> Value of Seed.
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("The seed used for randomizing the data when reduced-error pruning is used.")  </attribute>
		/// <property>   </property>
		public virtual int get_Seed()
		{
			
			return m_Seed;
		}
		
		/// <summary> Set the value of Seed.
		/// 
		/// </summary>
		/// <param name="newSeed">Value to assign to Seed.
		/// </param>
		/// <property>   </property>
		public virtual void  set_Seed(int newSeed)
		{
			
			m_Seed = newSeed;
		}
		
		
		
		/// <summary> Get the value of useLaplace.
		/// 
		/// </summary>
		/// <returns> Value of useLaplace.
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Whether counts at leaves are smoothed based on Laplace.")  </attribute>
		/// <property>   </property>
		public virtual bool get_UseLaplace()
		{
			
			return m_useLaplace;
		}
		
		/// <summary> Set the value of useLaplace.
		/// 
		/// </summary>
		/// <param name="newuseLaplace">Value to assign to useLaplace.
		/// </param>
		/// <property>   </property>
		public virtual void  set_UseLaplace(bool newuseLaplace)
		{
			
			m_useLaplace = newuseLaplace;
		}
		
		/// <summary> Returns a description of the classifier.</summary>
		public override System.String ToString()
		{
			if (m_root == null)
			{
				return "No classifier built";
			}
			if (m_unpruned)
			{
				return "J48 unpruned tree\n------------------\n" + m_root.ToString();
			}
			else
			{
				return "J48 pruned tree\n------------------\n" + m_root.ToString();
			}
		}
		
		/// <summary> Returns a superconcise version of the model</summary>
		public virtual System.String toSummaryString()
		{
			
			return "Number of leaves: " + m_root.numLeaves() + "\n" + "Size of the tree: " + m_root.numXmlNodes() + "\n";
		}
		
		/// <summary> Returns the size of the tree</summary>
		/// <returns> the size of the tree
		/// </returns>
		public virtual double measureTreeSize()
		{
			return m_root.numXmlNodes();
		}
		
		/// <summary> Returns the number of leaves</summary>
		/// <returns> the number of leaves
		/// </returns>
		public virtual double measureNumLeaves()
		{
			return m_root.numLeaves();
		}
		
		/// <summary> Returns the number of rules (same as number of leaves)</summary>
		/// <returns> the number of rules
		/// </returns>
		public virtual double measureNumRules()
		{
			return m_root.numLeaves();
		}
		
		/// <summary> Returns an enumeration of the additional measure names</summary>
		/// <returns> an enumeration of the measure names
		/// </returns>
		public virtual System.Collections.IEnumerator enumerateMeasures()
		{
			System.Collections.ArrayList newVector = System.Collections.ArrayList.Synchronized(new System.Collections.ArrayList(3));
			newVector.Add("measureTreeSize");
			newVector.Add("measureNumLeaves");
			newVector.Add("measureNumRules");
			return newVector.GetEnumerator();
		}
		
		/// <summary> Returns the value of the named measure</summary>
		/// <param name="measureName">the name of the measure to query for its value
		/// </param>
		/// <returns> the value of the named measure
		/// </returns>
		/// <exception cref="IllegalArgumentException">if the named measure is not supported
		/// </exception>
		public virtual double getMeasure(System.String additionalMeasureName)
		{
			if (System.String.Compare(additionalMeasureName, "measureNumRules", true) == 0)
			{
				return measureNumRules();
			}
			else if (System.String.Compare(additionalMeasureName, "measureTreeSize", true) == 0)
			{
				return measureTreeSize();
			}
			else if (System.String.Compare(additionalMeasureName, "measureNumLeaves", true) == 0)
			{
				return measureNumLeaves();
			}
			else
			{
				throw new System.ArgumentException(additionalMeasureName + " not supported (j48)");
			}
		}
		
		
		
		/// <summary> Get the value of unpruned.
		/// 
		/// </summary>
		/// <returns> Value of unpruned.
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Whether pruning is performed.")  </attribute>
		/// <property>   </property>
		public virtual bool get_Unpruned()
		{
			
			return m_unpruned;
		}
		
		/// <summary> Set the value of unpruned. Turns reduced-error pruning
		/// off if set.
		/// </summary>
		/// <param name="v"> Value to assign to unpruned.
		/// </param>
		/// <property>   </property>
		public virtual void  set_Unpruned(bool v)
		{
			
			if (v)
			{
				m_reducedErrorPruning = false;
			}
			m_unpruned = v;
		}
		
		
		
		/// <summary> Get the value of CF.
		/// 
		/// </summary>
		/// <returns> Value of CF.
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("The confidence factor used for pruning (smaller values incur more pruning).")  </attribute>
		/// <property>   </property>
		public virtual float get_ConfidenceFactor()
		{
			
			return m_CF;
		}
		
		/// <summary> Set the value of CF.
		/// 
		/// </summary>
		/// <param name="v"> Value to assign to CF.
		/// </param>
		/// <property>   </property>
		public virtual void  set_ConfidenceFactor(float v)
		{
			
			m_CF = v;
		}
		
		
		
		/// <summary> Get the value of minNumObj.
		/// 
		/// </summary>
		/// <returns> Value of minNumObj.
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("The minimum number of instances per leaf.")  </attribute>
		/// <property>   </property>
		public virtual int get_MinNumObj()
		{
			
			return m_minNumObj;
		}
		
		/// <summary> Set the value of minNumObj.
		/// 
		/// </summary>
		/// <param name="v"> Value to assign to minNumObj.
		/// </param>
		/// <property>   </property>
		public virtual void  set_MinNumObj(int v)
		{
			
			m_minNumObj = v;
		}
		
		
		
		/// <summary> Get the value of reducedErrorPruning. 
		/// 
		/// </summary>
		/// <returns> Value of reducedErrorPruning.
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Whether reduced-error pruning is used instead of C.4.5 pruning.")  </attribute>
		/// <property>   </property>
		public virtual bool get_ReducedErrorPruning()
		{
			
			return m_reducedErrorPruning;
		}
		
		/// <summary> Set the value of reducedErrorPruning. Turns
		/// unpruned trees off if set.
		/// 
		/// </summary>
		/// <param name="v"> Value to assign to reducedErrorPruning.
		/// </param>
		/// <property>   </property>
		public virtual void  set_ReducedErrorPruning(bool v)
		{
			
			if (v)
			{
				m_unpruned = false;
			}
			m_reducedErrorPruning = v;
		}
		
		
		
		/// <summary> Get the value of numFolds.
		/// 
		/// </summary>
		/// <returns> Value of numFolds.
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Determines the amount of data used for reduced-error pruning. One fold is used for pruning, the rest for growing the tree.")  </attribute>
		/// <property>   </property>
		public virtual int get_NumFolds()
		{
			
			return m_numFolds;
		}
		
		/// <summary> Set the value of numFolds.
		/// 
		/// </summary>
		/// <param name="v"> Value to assign to numFolds.
		/// </param>
		/// <property>   </property>
		public virtual void  set_NumFolds(int v)
		{
			
			m_numFolds = v;
		}
		
		
		
		/// <summary> Get the value of binarySplits.
		/// 
		/// </summary>
		/// <returns> Value of binarySplits.
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Whether to use binary splits on nominal attributes when building the trees.")  </attribute>
		/// <property>   </property>
		public virtual bool get_BinarySplits()
		{
			
			return m_binarySplits;
		}
		
		/// <summary> Set the value of binarySplits.
		/// 
		/// </summary>
		/// <param name="v"> Value to assign to binarySplits.
		/// </param>
		/// <property>   </property>
		public virtual void  set_BinarySplits(bool v)
		{
			
			m_binarySplits = v;
		}
		
		
		
		/// <summary> Get the value of subtreeRaising.
		/// 
		/// </summary>
		/// <returns> Value of subtreeRaising.
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Whether to consider the subtree raising operation when pruning.")  </attribute>
		/// <property>   </property>
		public virtual bool get_SubtreeRaising()
		{
			
			return m_subtreeRaising;
		}
		
		/// <summary> Set the value of subtreeRaising.
		/// 
		/// </summary>
		/// <param name="v"> Value to assign to subtreeRaising.
		/// </param>
		/// <property>   </property>
		public virtual void  set_SubtreeRaising(bool v)
		{
			
			m_subtreeRaising = v;
		}
		
		
		
		/// <summary> Check whether instance data is to be saved.
		/// 
		/// </summary>
		/// <returns> true if instance data is saved
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Whether to save the training data for visualization.")  </attribute>
		/// <property>   </property>
		public virtual bool get_SaveInstanceData()
		{
			
			return m_noCleanup;
		}
		
		/// <summary> Set whether instance data is to be saved.</summary>
		/// <param name="v">true if instance data is to be saved
		/// </param>
		/// <property>   </property>
		public virtual void  set_SaveInstanceData(bool v)
		{
			
			m_noCleanup = v;
		}
#if PocketPC
        override public System.Object Clone()
        {
            return null;
        }
#else
		//UPGRADE_TODO: The following method was automatically generated and it must be implemented in order to preserve the class logic. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1232'"
		override public System.Object Clone()
		{

            MemoryStream ms = new MemoryStream();
            BinaryFormatter bf = new BinaryFormatter();
            bf.Serialize(ms, this);
            ms.Position = 0;
            object obj = bf.Deserialize(ms);
            ms.Close();

            return obj;
		}
#endif
	}
}