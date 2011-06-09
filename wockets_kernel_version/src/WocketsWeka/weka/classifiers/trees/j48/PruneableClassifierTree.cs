/*
*    PruneableClassifierTree.java
*    Copyright (C) 1999 Eibe Frank
*
*/
using System;
using weka.core;
namespace weka.classifiers.trees.j48
{
	
	/// <summary> Class for handling a tree structure that can
	/// be pruned using a pruning set. 
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.8 $
	/// </version>
	public class PruneableClassifierTree:ClassifierTree
	{
		
		/// <summary>True if the tree is to be pruned. </summary>
		private bool pruneTheTree = false;
		
		/// <summary>How many subsets of equal size? One used for pruning, the rest for training. </summary>
		private int numSets = 3;
		
		/// <summary>Cleanup after the tree has been built. </summary>
		private bool m_cleanup = true;
		
		/// <summary>The random number seed. </summary>
		private int m_seed = 1;
		
		/// <summary> Constructor for pruneable tree structure. Stores reference
		/// to associated training data at each node.
		/// 
		/// </summary>
		/// <param name="toSelectLocModel">selection method for local splitting model
		/// </param>
		/// <param name="pruneTree">true if the tree is to be pruned
		/// </param>
		/// <param name="num">number of subsets of equal size
		/// </param>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public PruneableClassifierTree(ModelSelection toSelectLocModel, bool pruneTree, int num, bool cleanup, int seed):base(toSelectLocModel)
		{
			
			pruneTheTree = pruneTree;
			numSets = num;
			m_cleanup = cleanup;
			m_seed = seed;
		}
		
		/// <summary> Method for building a pruneable classifier tree.
		/// 
		/// </summary>
		/// <exception cref="Exception">if tree can't be built successfully
		/// </exception>
		public override void  buildClassifier(Instances data)
		{
			
			if (data.classAttribute().Numeric)
				throw new System.Exception("Class is numeric!");
			
			data = new Instances(data);
			//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.util.Random.Random'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
			System.Random random = new System.Random((System.Int32) m_seed);
			data.deleteWithMissingClass();
			data.stratify(numSets);
			buildTree(data.trainCV(numSets, numSets - 1, random), data.testCV(numSets, numSets - 1), false);
			if (pruneTheTree)
			{
				prune();
			}
			if (m_cleanup)
			{
				cleanup(new Instances(data, 0));
			}
		}
		
		/// <summary> Prunes a tree.
		/// 
		/// </summary>
		/// <exception cref="Exception">if tree can't be pruned successfully
		/// </exception>
		public virtual void  prune()
		{
			
			if (!m_isLeaf)
			{
				
				// Prune all subtrees.
				for (int i = 0; i < m_sons.Length; i++)
					son(i).prune();
				
				// Decide if leaf is best choice.
				if (Utils.smOrEq(errorsForLeaf(), errorsForTree()))
				{
					
					// Free son Trees
					m_sons = null;
					m_isLeaf = true;
					
					// Get NoSplit Model for node.
					m_localModel = new NoSplit(localModel().distribution());
				}
			}
		}
		
		/// <summary> Returns a newly created tree.
		/// 
		/// </summary>
		/// <param name="data">and selection method for local models.
		/// </param>
		protected internal override ClassifierTree getNewTree(Instances train, Instances test)
		{
			
			PruneableClassifierTree newTree = new PruneableClassifierTree(m_toSelectModel, pruneTheTree, numSets, m_cleanup, m_seed);
			newTree.buildTree(train, test, false);
			return newTree;
		}
		
		/// <summary> Computes estimated errors for tree.
		/// 
		/// </summary>
		/// <exception cref="Exception">if error estimate can't be computed
		/// </exception>
		private double errorsForTree()
		{
			
			double errors = 0;
			
			if (m_isLeaf)
				return errorsForLeaf();
			else
			{
				for (int i = 0; i < m_sons.Length; i++)
					if (Utils.eq(localModel().distribution().perBag(i), 0))
					{
						errors += m_test.perBag(i) - m_test.perClassPerBag(i, localModel().distribution().maxClass());
					}
					else
						errors += son(i).errorsForTree();
				
				return errors;
			}
		}
		
		/// <summary> Computes estimated errors for leaf.
		/// 
		/// </summary>
		/// <exception cref="Exception">if error estimate can't be computed
		/// </exception>
		private double errorsForLeaf()
		{
			
			return m_test.total() - m_test.perClass(localModel().distribution().maxClass());
		}
		
		/// <summary> Method just exists to make program easier to read.</summary>
		private ClassifierSplitModel localModel()
		{
			
			return (ClassifierSplitModel) m_localModel;
		}
		
		/// <summary> Method just exists to make program easier to read.</summary>
		private PruneableClassifierTree son(int index)
		{
			
			return (PruneableClassifierTree) m_sons[index];
		}
	}
}