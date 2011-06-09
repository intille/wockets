/*
*    ClassifierTree.java
*    Copyright (C) 1999 Eibe Frank
*/
using System;
using weka.core;
using weka.classifiers;
using weka.support;
using System.Xml.Serialization;
using System.IO;

namespace weka.classifiers.trees.j48
{
	
	/// <summary> Class for handling a tree structure used for
	/// classification.
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.17 $
	/// </version>
    /// 
#if !PocketPC
    [Serializable()]  
#endif
	public class ClassifierTree : Drawable, ITree
	{
		//code of alain espinosa
		public virtual Node FirstNode()
		{
			Node _result = null;
			
			try
			{
				if (m_isLeaf)
				{
					_result = new Node(m_localModel.dumpLabel(0, m_train));
				}
				else
				{
					_result = new weka.support.Node(m_localModel.leftSide(m_train));
					
					for (int i = 0; i < m_sons.Length; i++)
					{
						_result.AddChild(m_localModel.rightSide(i, m_train), m_sons[i].FirstNode());
					}
				}
			}
			catch (System.Exception)
			{
			}
			
			return _result;
		}
		public virtual System.String DescriptionTree()
		{
			return "\n--------------\nClassifing by: " + m_train.attribute(m_train.classIndex()).name() + "\nDataset: " + m_train.relationName();
		}
		//edn of code
		/// <summary>The model selection method. </summary>
		protected internal ModelSelection m_toSelectModel;
		/// <summary>Local model at node. </summary>
		protected internal ClassifierSplitModel m_localModel;
		/// <summary>References to sons. </summary>
		protected internal ClassifierTree[] m_sons;
		/// <summary>True if node is leaf. </summary>
		protected internal bool m_isLeaf;
		/// <summary>True if node is empty. </summary>
		protected internal bool m_isEmpty;
		/// <summary>The training instances. </summary>
		protected internal Instances m_train;
		/// <summary>The pruning instances. </summary>
		protected internal Distribution m_test;
		/// <summary>The id for the node. </summary>
		protected internal int m_id;
		/// <summary> For getting a unique ID when outputting the tree (hashcode isn't
		/// guaranteed unique) 
		/// </summary>
		private static long PRINTED_NODES = 0;
		

		/// <summary> Gets the next unique node ID.
		/// 
		/// </summary>
		/// <returns> the next unique node ID.
		/// </returns>
		protected internal static long nextID()
		{
			
			return PRINTED_NODES++;
		}
		
		/// <summary> Resets the unique node ID counter (e.g.
		/// between repeated separate print types)
		/// </summary>
		protected internal static void  resetID()
		{
			
			PRINTED_NODES = 0;
		}

        public ClassifierTree()
        {

        }
		/// <summary> Constructor. </summary>
		public ClassifierTree(ModelSelection toSelectLocModel)
		{
			
			m_toSelectModel = toSelectLocModel;
		}


        public virtual void toXML(TextWriter tw)
        {
        }
		/// <summary> Method for building a classifier tree.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public virtual void  buildClassifier(Instances data)
		{
			
			if (data.checkForStringAttributes())
			{
				throw new Exception("Cannot handle string attributes!");
			}
			data = new Instances(data);
			data.deleteWithMissingClass();
			buildTree(data, false);
		}
		
		/// <summary> Builds the tree structure.
		/// 
		/// </summary>
		/// <param name="data">the data for which the tree structure is to be
		/// generated.
		/// </param>
		/// <param name="keepData">is training data to be kept?
		/// </param>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public virtual void  buildTree(Instances data, bool keepData)
		{
			
			Instances[] localInstances;
			
			if (keepData)
			{
				m_train = data;
			}
			m_test = null;
			m_isLeaf = false;
			m_isEmpty = false;
			m_sons = null;
			m_localModel = m_toSelectModel.selectModel(data);
			if (m_localModel.numSubsets() > 1)
			{
				localInstances = m_localModel.split(data);
				data = null;
				m_sons = new ClassifierTree[m_localModel.numSubsets()];
				for (int i = 0; i < m_sons.Length; i++)
				{
					m_sons[i] = getNewTree(localInstances[i]);
					localInstances[i] = null;
				}
			}
			else
			{
				m_isLeaf = true;
				if (Utils.eq(data.sumOfWeights(), 0))
					m_isEmpty = true;
				data = null;
			}
		}
		
		/// <summary> Builds the tree structure with hold out set
		/// 
		/// </summary>
		/// <param name="train">the data for which the tree structure is to be
		/// generated.
		/// </param>
		/// <param name="test">the test data for potential pruning
		/// </param>
		/// <param name="keepData">is training Data to be kept?
		/// </param>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public virtual void  buildTree(Instances train, Instances test, bool keepData)
		{
			
			Instances[] localTrain, localTest;
			int i;
			
			if (keepData)
			{
				m_train = train;
			}
			m_isLeaf = false;
			m_isEmpty = false;
			m_sons = null;
			m_localModel = m_toSelectModel.selectModel(train, test);
			m_test = new Distribution(test, m_localModel);
			if (m_localModel.numSubsets() > 1)
			{
				localTrain = m_localModel.split(train);
				localTest = m_localModel.split(test);
				train = test = null;
				m_sons = new ClassifierTree[m_localModel.numSubsets()];
				for (i = 0; i < m_sons.Length; i++)
				{
					m_sons[i] = getNewTree(localTrain[i], localTest[i]);
					localTrain[i] = null;
					localTest[i] = null;
				}
			}
			else
			{
				m_isLeaf = true;
				if (Utils.eq(train.sumOfWeights(), 0))
					m_isEmpty = true;
				train = test = null;
			}
		}
		
		/// <summary> Classifies an instance.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public virtual double classifyInstance(Instance instance)
		{
			
			double maxProb = - 1;
			double currentProb;
			int maxIndex = 0;
			int j;
			
			for (j = 0; j < instance.numClasses(); j++)
			{
				currentProb = getProbs(j, instance, 1);
				if (Utils.gr(currentProb, maxProb))
				{
					maxIndex = j;
					maxProb = currentProb;
				}
			}
			
			return (double) maxIndex;
		}
		
		/// <summary> Cleanup in order to save memory.</summary>
		public void  cleanup(Instances justHeaderInfo)
		{
			
			m_train = justHeaderInfo;
			m_test = null;
			if (!m_isLeaf)
				for (int i = 0; i < m_sons.Length; i++)
					m_sons[i].cleanup(justHeaderInfo);
		}
		
		/// <summary> Returns class probabilities for a weighted instance.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public double[] distributionForInstance(Instance instance, bool useLaplace)
		{
			
			double[] doubles = new double[instance.numClasses()];
			
			for (int i = 0; i < doubles.Length; i++)
			{
				if (!useLaplace)
				{
					doubles[i] = getProbs(i, instance, 1);
				}
				else
				{
					doubles[i] = getProbsLaplace(i, instance, 1);
				}
			}
			
			return doubles;
		}
		
		/// <summary> Assigns a uniqe id to every node in the tree.</summary>
		public virtual int assignIDs(int lastID)
		{
			
			int currLastID = lastID + 1;
			
			m_id = currLastID;
			if (m_sons != null)
			{
				for (int i = 0; i < m_sons.Length; i++)
				{
					currLastID = m_sons[i].assignIDs(currLastID);
				}
			}
			return currLastID;
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
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public virtual System.String graph()
		{
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			
			assignIDs(- 1);
			text.Append("digraph J48Tree {\n");
			if (m_isLeaf)
			{
				text.Append("N" + m_id + " [label=\"" + m_localModel.dumpLabel(0, m_train) + "\" " + "shape=box style=filled ");
				if (m_train != null && m_train.numInstances() > 0)
				{
					text.Append("data =\n" + m_train + "\n");
					text.Append(",\n");
				}
				text.Append("]\n");
			}
			else
			{
				text.Append("N" + m_id + " [label=\"" + m_localModel.leftSide(m_train) + "\" ");
				if (m_train != null && m_train.numInstances() > 0)
				{
					text.Append("data =\n" + m_train + "\n");
					text.Append(",\n");
				}
				text.Append("]\n");
				graphTree(text);
			}
			
			return text.ToString() + "}\n";
		}
		
		/// <summary> Returns tree in prefix order.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public virtual System.String prefix()
		{
			
			System.Text.StringBuilder text;
			
			text = new System.Text.StringBuilder();
			if (m_isLeaf)
			{
				text.Append("[" + m_localModel.dumpLabel(0, m_train) + "]");
			}
			else
			{
				prefixTree(text);
			}
			
			return text.ToString();
		}
		
		/// <summary> Returns source code for the tree as an if-then statement. The 
		/// class is assigned to variable "p", and assumes the tested 
		/// instance is named "i". The results are returned as two stringbuffers: 
		/// a section of code for assignment of the class, and a section of
		/// code containing support code (eg: other support methods).
		/// 
		/// </summary>
		/// <param name="className">the classname that this static classifier has
		/// </param>
		/// <returns> an array containing two stringbuffers, the first string containing
		/// assignment code, and the second containing source for support code.
		/// </returns>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public virtual System.Text.StringBuilder[] toSource(System.String className)
		{
			
			System.Text.StringBuilder[] result = new System.Text.StringBuilder[2];
			if (m_isLeaf)
			{
				result[0] = new System.Text.StringBuilder("    p = " + m_localModel.distribution().maxClass(0) + ";\n");
				result[1] = new System.Text.StringBuilder("");
			}
			else
			{
				System.Text.StringBuilder text = new System.Text.StringBuilder();
				//String nextIndent = "      ";
				System.Text.StringBuilder atEnd = new System.Text.StringBuilder();
				
				long printID = ClassifierTree.nextID();
				
				text.Append("  static double N").Append(System.Convert.ToString(m_localModel.GetHashCode(), 16) + printID).Append("(Object []i) {\n").Append("    double p = Double.NaN;\n");
				
				text.Append("    if (").Append(m_localModel.sourceExpression(- 1, m_train)).Append(") {\n");
				text.Append("      p = ").Append(m_localModel.distribution().maxClass(0)).Append(";\n");
				text.Append("    } ");
				for (int i = 0; i < m_sons.Length; i++)
				{
					text.Append("else if (" + m_localModel.sourceExpression(i, m_train) + ") {\n");
					if (m_sons[i].m_isLeaf)
					{
						text.Append("      p = " + m_localModel.distribution().maxClass(i) + ";\n");
					}
					else
					{
						System.Text.StringBuilder[] sub = m_sons[i].toSource(className);
						text.Append(sub[0]);
						atEnd.Append(sub[1]);
					}
					text.Append("    } ");
					if (i == m_sons.Length - 1)
					{
						text.Append('\n');
					}
				}
				
				text.Append("    return p;\n  }\n");
				
				result[0] = new System.Text.StringBuilder("    p = " + className + ".N");
				result[0].Append(System.Convert.ToString(m_localModel.GetHashCode(), 16) + printID).Append("(i);\n");
				result[1] = text.Append(atEnd);
			}
			return result;
		}
		
		/// <summary> Returns number of leaves in tree structure.</summary>
		public virtual int numLeaves()
		{
			
			int num = 0;
			int i;
			
			if (m_isLeaf)
				return 1;
			else
				for (i = 0; i < m_sons.Length; i++)
					num = num + m_sons[i].numLeaves();
			
			return num;
		}
		
		/// <summary> Returns number of nodes in tree structure.</summary>
		public virtual int numXmlNodes()
		{
			
			int no = 1;
			int i;
			
			if (!m_isLeaf)
				for (i = 0; i < m_sons.Length; i++)
					no = no + m_sons[i].numXmlNodes();
			
			return no;
		}
		
		/// <summary> Prints tree structure.</summary>
		public override System.String ToString()
		{
			try
			{
				System.Text.StringBuilder text = new System.Text.StringBuilder();
				
				if (m_isLeaf)
				{
					text.Append(": ");
					text.Append(m_localModel.dumpLabel(0, m_train));
				}
				else
					dumpTree(0, text);
				text.Append("\n\nNumber of Leaves  : \t" + numLeaves() + "\n");
				text.Append("\nSize of the tree : \t" + numXmlNodes() + "\n");
				
				return text.ToString();
			}
			catch (System.Exception)
			{
				return "Can't print classification tree.";
			}
		}
		
		/// <summary> Returns a newly created tree.
		/// 
		/// </summary>
		/// <param name="data">the training data
		/// </param>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		protected internal virtual ClassifierTree getNewTree(Instances data)
		{
			
			ClassifierTree newTree = new ClassifierTree(m_toSelectModel);
			newTree.buildTree(data, false);
			
			return newTree;
		}
		
		/// <summary> Returns a newly created tree.
		/// 
		/// </summary>
		/// <param name="data">the training data
		/// </param>
		/// <param name="test">the pruning data.
		/// </param>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		protected internal virtual ClassifierTree getNewTree(Instances train, Instances test)
		{
			
			ClassifierTree newTree = new ClassifierTree(m_toSelectModel);
			newTree.buildTree(train, test, false);
			
			return newTree;
		}
		
		/// <summary> Help method for printing tree structure.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		private void  dumpTree(int depth, System.Text.StringBuilder text)
		{
			int i, j;
			
			for (i = 0; i < m_sons.Length; i++)
			{
				text.Append("\n"); ;
				for (j = 0; j < depth; j++)
					text.Append("|   ");
				text.Append(m_localModel.leftSide(m_train));
				text.Append(m_localModel.rightSide(i, m_train));
				if (m_sons[i].m_isLeaf)
				{
					text.Append(": ");
					text.Append(m_localModel.dumpLabel(i, m_train));
				}
				else
					m_sons[i].dumpTree(depth + 1, text);
			}
		}
		
		/// <summary> Help method for printing tree structure as a graph.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		private void  graphTree(System.Text.StringBuilder text)
		{
			
			for (int i = 0; i < m_sons.Length; i++)
			{
				text.Append("N" + m_id + "->" + "N" + m_sons[i].m_id + " [label=\"" + m_localModel.rightSide(i, m_train).Trim() + "\"]\n");
				if (m_sons[i].m_isLeaf)
				{
					text.Append("N" + m_sons[i].m_id + " [label=\"" + m_localModel.dumpLabel(i, m_train) + "\" " + "shape=box style=filled ");
					if (m_train != null && m_train.numInstances() > 0)
					{
						text.Append("data =\n" + m_sons[i].m_train + "\n");
						text.Append(",\n");
					}
					text.Append("]\n");
				}
				else
				{
					text.Append("N" + m_sons[i].m_id + " [label=\"" + m_sons[i].m_localModel.leftSide(m_train) + "\" ");
					if (m_train != null && m_train.numInstances() > 0)
					{
						text.Append("data =\n" + m_sons[i].m_train + "\n");
						text.Append(",\n");
					}
					text.Append("]\n");
					m_sons[i].graphTree(text);
				}
			}
		}
		
		/// <summary> Prints the tree in prefix form</summary>
		private void  prefixTree(System.Text.StringBuilder text)
		{
			
			text.Append("[");
			text.Append(m_localModel.leftSide(m_train) + ":");
			for (int i = 0; i < m_sons.Length; i++)
			{
				if (i > 0)
				{
					text.Append(",\n");
				}
				text.Append(m_localModel.rightSide(i, m_train));
			}
			for (int i = 0; i < m_sons.Length; i++)
			{
				if (m_sons[i].m_isLeaf)
				{
					text.Append("[");
					text.Append(m_localModel.dumpLabel(i, m_train));
					text.Append("]");
				}
				else
				{
					m_sons[i].prefixTree(text);
				}
			}
			text.Append("]");
		}
		
		/// <summary> Help method for computing class probabilities of 
		/// a given instance.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		private double getProbsLaplace(int classIndex, Instance instance, double weight)
		{
			double[] weights;
			double prob = 0;
			int treeIndex;
			int i;
			
			if (m_isLeaf)
			{
				return weight * localModel().classProbLaplace(classIndex, instance, - 1);
			}
			else
			{
				treeIndex = localModel().whichSubset(instance);
				if (treeIndex == - 1)
				{
					weights = localModel().GetWeights(instance);
					for (i = 0; i < m_sons.Length; i++)
					{
						if (!son(i).m_isEmpty)
						{
							if (!son(i).m_isLeaf)
							{
								prob += son(i).getProbsLaplace(classIndex, instance, weights[i] * weight);
							}
							else
							{
								prob += weight * weights[i] * localModel().classProbLaplace(classIndex, instance, i);
							}
						}
					}
					return prob;
				}
				else
				{
					if (son(treeIndex).m_isLeaf)
					{
						return weight * localModel().classProbLaplace(classIndex, instance, treeIndex);
					}
					else
					{
						return son(treeIndex).getProbsLaplace(classIndex, instance, weight);
					}
				}
			}
		}
		
		/// <summary> Help method for computing class probabilities of 
		/// a given instance.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		private double getProbs(int classIndex, Instance instance, double weight)
		{
			
			double[] weights;
			double prob = 0;
			int treeIndex;
			int i;
			
			if (m_isLeaf)
			{
				return weight * localModel().classProb(classIndex, instance, - 1);
			}
			else
			{
				treeIndex = localModel().whichSubset(instance);
				if (treeIndex == - 1)
				{
					weights = localModel().GetWeights(instance);
					for (i = 0; i < m_sons.Length; i++)
					{
						if (!son(i).m_isEmpty)
						{
							prob += son(i).getProbs(classIndex, instance, weights[i] * weight);
						}
					}
					return prob;
				}
				else
				{
					if (son(treeIndex).m_isEmpty)
					{
						return weight * localModel().classProb(classIndex, instance, treeIndex);
					}
					else
					{
						return son(treeIndex).getProbs(classIndex, instance, weight);
					}
				}
			}
		}
		
		/// <summary> Method just exists to make program easier to read.</summary>
		private ClassifierSplitModel localModel()
		{
			
			return (ClassifierSplitModel) m_localModel;
		}
		
		/// <summary> Method just exists to make program easier to read.</summary>
		private ClassifierTree son(int index)
		{
			return (ClassifierTree) m_sons[index];
		}
	}
}