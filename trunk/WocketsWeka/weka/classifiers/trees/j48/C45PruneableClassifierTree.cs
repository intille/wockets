/*
*    C45PruneableClassifierTree.java
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
	
	/// <summary> Class for handling a tree structure that can
	/// be pruned using C4.5 procedures.
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.11 $
	/// </version>
#if !PocketPC
    [Serializable()]  
#endif
	public class C45PruneableClassifierTree:ClassifierTree
	{
		/// <summary> Computes estimated errors for tree.</summary>
		private double EstimatedErrors
		{
			get
			{
				double errors = 0;
				int i;
				
				if (m_isLeaf)
					return getEstimatedErrorsForDistribution(localModel().distribution());
				else
				{
					for (i = 0; i < m_sons.Length; i++)
						errors = errors + son(i).EstimatedErrors;
					return errors;
				}
			}
			
		}
		/// <summary> Computes errors of tree on training data.</summary>
		private double TrainingErrors
		{
			get
			{
				double errors = 0;
				int i;
				
				if (m_isLeaf)
					return localModel().distribution().numIncorrect();
				else
				{
					for (i = 0; i < m_sons.Length; i++)
						errors = errors + son(i).TrainingErrors;
					return errors;
				}
			}
			
		}
		
		/// <summary>True if the tree is to be pruned. </summary>
		internal bool m_pruneTheTree = false;
		
		/// <summary>The confidence factor for pruning. </summary>
		internal float m_CF = 0.25f;
		
		/// <summary>Is subtree raising to be performed? </summary>
		internal bool m_subtreeRaising = true;
		
		/// <summary>Cleanup after the tree has been built. </summary>
		internal bool m_cleanup = true;
		
		/// <summary> Constructor for pruneable tree structure. Stores reference
		/// to associated training data at each node.
		/// 
		/// </summary>
		/// <param name="toSelectLocModel">selection method for local splitting model
		/// </param>
		/// <param name="pruneTree">true if the tree is to be pruned
		/// </param>
		/// <param name="cf">the confidence factor for pruning
		/// </param>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public C45PruneableClassifierTree(ModelSelection toSelectLocModel, bool pruneTree, float cf, bool raiseTree, bool cleanup):base(toSelectLocModel)
		{
			
			m_pruneTheTree = pruneTree;
			m_CF = cf;
			m_subtreeRaising = raiseTree;
			m_cleanup = cleanup;
		}

        /// <summary>The model selection method. </summary>
        //protected internal ModelSelection m_toSelectModel;
        /// <summary>Local model at node. </summary>
        //protected internal ClassifierSplitModel m_localModel;
        /// <summary>References to sons. </summary>
        //protected internal ClassifierTree[] m_sons;

        public C45PruneableClassifierTree(XmlNode root, Instances allData)
        {
            if (root.Name == Constants.C45_PRUNEABLE_ELEMENT)
            {

                foreach (XmlAttribute xAttribute in root.Attributes)
                {
                    if (xAttribute.Name == Constants.PRUNE_THE_TREE)
                    {
                        if (xAttribute.Value == "True")
                            this.m_pruneTheTree = true;
                        else
                            this.m_pruneTheTree = false;
                    }
                    else if (xAttribute.Name == Constants.CONFIDENCE_ATTRIBUTE)
                        this.m_CF = (float)Convert.ToDouble(xAttribute.Value);
                    else if (xAttribute.Name == Constants.SUBTREE_RAISING_ATTRIBUTE)
                    {
                        if (xAttribute.Value == "True")
                            this.m_subtreeRaising = true;
                        else
                            this.m_subtreeRaising = false;
                    }
                    else if (xAttribute.Name == Constants.CLEANUP_ATTRIBUTE)
                    {
                        if (xAttribute.Value == "True")
                            this.m_cleanup = true;
                        else
                            this.m_cleanup = false;
                    }
                    else if (xAttribute.Name == Constants.ISLEAF_ATTRIBUTE)
                    {
                        if (xAttribute.Value == "True")
                            this.m_isLeaf = true;
                        else
                            this.m_isLeaf = false;
                    }
                    else if (xAttribute.Name == Constants.ISEMPTY_ATTRIBUTE)
                    {
                        if (xAttribute.Value == "True")
                            this.m_isEmpty = true;
                        else
                            this.m_isEmpty = false;
                    }
                    else if (xAttribute.Name == Constants.TREE_ID_ATTRIBUTE)
                        this.m_id = Convert.ToInt32(xAttribute.Value);


                }

                int i = 0;
                //Going through the subtrees
                foreach (XmlNode iNode in root.ChildNodes)
                {
                    if (iNode.Name == Constants.C45MODELSELECTION_ELEMENT)
                        this.m_toSelectModel = new C45ModelSelection(iNode, allData);
                    else if (iNode.Name == Constants.BINC45MODELSELECTION_ELEMENT)
                        this.m_toSelectModel = new BinC45ModelSelection(iNode, allData);
                    else if (iNode.Name == Constants.NOSPLIT_ELEMENT)
                        this.m_localModel = new NoSplit(iNode);
                    else if (iNode.Name == Constants.C45SPLIT_ELEMENT)
                        this.m_localModel = new C45Split(iNode);
                    else if (iNode.Name == Constants.BINC45SPLIT_ELEMENT)
                        this.m_localModel = new BinC45Split(iNode);
                    else if (iNode.Name == Constants.C45_PRUNEABLE_ELEMENT)
                    {
                        if ((this.m_sons == null) || (this.m_sons.Length <= 0))
                            this.m_sons = new ClassifierTree[2];
                        this.m_sons[i] = new C45PruneableClassifierTree(iNode, allData);
                        i++;
                    }
                }
            }
        }
        public override void toXML(TextWriter tw)
        {

           tw.WriteLine("<" + Constants.C45_PRUNEABLE_ELEMENT + " " +
        Constants.PRUNE_THE_TREE + "=\"" + this.m_pruneTheTree + "\"   " +
        Constants.CONFIDENCE_ATTRIBUTE + "=\"" + this.m_CF + "\"   " +
        Constants.SUBTREE_RAISING_ATTRIBUTE + "=\"" + this.m_subtreeRaising + "\"   " +
        Constants.CLEANUP_ATTRIBUTE + "=\"" + this.m_cleanup + "\"   " +
        Constants.ISLEAF_ATTRIBUTE + "=\"" + this.m_isLeaf + "\"   " +
        Constants.ISEMPTY_ATTRIBUTE + "=\"" + this.m_isEmpty + "\"   " +
        Constants.TREE_ID_ATTRIBUTE + "=\"" + this.m_id + "\"   " +
        " xmlns=\"urn:mites-schema\">\n");
            m_toSelectModel.toXML(tw);
            m_localModel.toXML(tw);
            if (m_sons != null)
            {
                for (int i = 0; (i < m_sons.Length); i++)
                    m_sons[i].toXML(tw);
            }
            tw.WriteLine("</" + Constants.C45_PRUNEABLE_ELEMENT + ">\n");
   
        }
		/// <summary> Method for building a pruneable classifier tree.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public override void  buildClassifier(Instances data)
		{
			
			if (data.classAttribute().Numeric)
				throw new Exception("Class is numeric!");
			if (data.checkForStringAttributes())
			{
				throw new Exception("Cannot handle string attributes!");
			}
			data = new Instances(data);
			data.deleteWithMissingClass();
			buildTree(data, m_subtreeRaising);
			collapse();
			if (m_pruneTheTree)
			{
				prune();
			}
			if (m_cleanup)
			{
				cleanup(new Instances(data, 0));
			}
		}
		
		/// <summary> Collapses a tree to a node if training error doesn't increase.</summary>
		public void  collapse()
		{
			
			double errorsOfSubtree;
			double errorsOfTree;
			int i;
			
			if (!m_isLeaf)
			{
				errorsOfSubtree = TrainingErrors;
				errorsOfTree = localModel().distribution().numIncorrect();
				if (errorsOfSubtree >= errorsOfTree - 1e-3)
				{
					
					// Free adjacent trees
					m_sons = null;
					m_isLeaf = true;
					
					// Get NoSplit Model for tree.
					m_localModel = new NoSplit(localModel().distribution());
				}
				else
					for (i = 0; i < m_sons.Length; i++)
						son(i).collapse();
			}
		}
		
		/// <summary> Prunes a tree using C4.5's pruning procedure.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public virtual void  prune()
		{
			
			double errorsLargestBranch;
			double errorsLeaf;
			double errorsTree;
			int indexOfLargestBranch;
			C45PruneableClassifierTree largestBranch;
			int i;
			
			if (!m_isLeaf)
			{
				
				// Prune all subtrees.
				for (i = 0; i < m_sons.Length; i++)
					son(i).prune();
				
				// Compute error for largest branch
				indexOfLargestBranch = localModel().distribution().maxBag();
				if (m_subtreeRaising)
				{
					errorsLargestBranch = son(indexOfLargestBranch).getEstimatedErrorsForBranch((Instances) m_train);
				}
				else
				{
					//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
					errorsLargestBranch = System.Double.MaxValue;
				}
				
				// Compute error if this Tree would be leaf
				errorsLeaf = getEstimatedErrorsForDistribution(localModel().distribution());
				
				// Compute error for the whole subtree
				errorsTree = EstimatedErrors;
				
				// Decide if leaf is best choice.
				if (Utils.smOrEq(errorsLeaf, errorsTree + 0.1) && Utils.smOrEq(errorsLeaf, errorsLargestBranch + 0.1))
				{
					
					// Free son Trees
					m_sons = null;
					m_isLeaf = true;
					
					// Get NoSplit Model for node.
					m_localModel = new NoSplit(localModel().distribution());
					return ;
				}
				
				// Decide if largest branch is better choice
				// than whole subtree.
				if (Utils.smOrEq(errorsLargestBranch, errorsTree + 0.1))
				{
					largestBranch = son(indexOfLargestBranch);
					m_sons = largestBranch.m_sons;
					m_localModel = largestBranch.localModel();
					m_isLeaf = largestBranch.m_isLeaf;
					newDistribution(m_train);
					prune();
				}
			}
		}
		
		/// <summary> Returns a newly created tree.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		protected internal override ClassifierTree getNewTree(Instances data)
		{
			
			C45PruneableClassifierTree newTree = new C45PruneableClassifierTree(m_toSelectModel, m_pruneTheTree, m_CF, m_subtreeRaising, m_cleanup);
			newTree.buildTree((Instances) data, m_subtreeRaising);
			
			return newTree;
		}
		
		/// <summary> Computes estimated errors for one branch.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		private double getEstimatedErrorsForBranch(Instances data)
		{
			Instances[] localInstances;
			double errors = 0;
			int i;
			
			if (m_isLeaf)
				return getEstimatedErrorsForDistribution(new Distribution(data));
			else
			{
				Distribution savedDist = localModel().m_distribution;
				localModel().resetDistribution(data);
				localInstances = (Instances[]) localModel().split(data);
				localModel().m_distribution = savedDist;
				for (i = 0; i < m_sons.Length; i++)
					errors = errors + son(i).getEstimatedErrorsForBranch(localInstances[i]);
				return errors;
			}
		}
		
		/// <summary> Computes estimated errors for leaf.</summary>
		private double getEstimatedErrorsForDistribution(Distribution theDistribution)
		{
			
			if (Utils.eq(theDistribution.total(), 0))
				return 0;
			else
				return theDistribution.numIncorrect() + Stats.addErrs(theDistribution.total(), theDistribution.numIncorrect(), m_CF);
		}
		
		/// <summary> Method just exists to make program easier to read.</summary>
		private ClassifierSplitModel localModel()
		{
			
			return (ClassifierSplitModel) m_localModel;
		}
		
		/// <summary> Computes new distributions of instances for nodes
		/// in tree.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		private void  newDistribution(Instances data)
		{
			
			Instances[] localInstances;
			
			localModel().resetDistribution(data);
			m_train = data;
			if (!m_isLeaf)
			{
				localInstances = (Instances[]) localModel().split(data);
				for (int i = 0; i < m_sons.Length; i++)
					son(i).newDistribution(localInstances[i]);
			}
			else
			{
				
				// Check whether there are some instances at the leaf now!
				if (!Utils.eq(data.sumOfWeights(), 0))
				{
					m_isEmpty = false;
				}
			}
		}
		
		/// <summary> Method just exists to make program easier to read.</summary>
		private C45PruneableClassifierTree son(int index)
		{
			
			return (C45PruneableClassifierTree) m_sons[index];
		}
	}
}