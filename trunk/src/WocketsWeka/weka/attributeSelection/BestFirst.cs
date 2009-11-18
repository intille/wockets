/*
*    This program is free software; you can redistribute it and/or modify
*    it under the terms of the GNU General Public License as published by
*    the Free Software Foundation; either version 2 of the License, or
*    (at your option) any later version.
*
*    This program is distributed in the hope that it will be useful,
*    but WITHOUT ANY WARRANTY; without even the implied warranty of
*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
*    GNU General Public License for more details.
*
*    You should have received a copy of the GNU General Public License
*    along with this program; if not, write to the Free Software
*    Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
*/

/*
*    BestFirst.java
*    Copyright (C) 1999 Mark Hall
*
*/
using System;
//UPGRADE_TODO: The package 'weka.core' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using weka.core;
namespace weka.attributeSelection
{
	
	/// <summary> Class for performing a best first search. <p>
	/// 
	/// Valid options are: <p>
	/// 
	/// -P <start set> <br>
	/// Specify a starting set of attributes. Eg 1,4,7-9. <p>
	/// 
	/// -D <-1 = backward | 0 = bidirectional | 1 = forward> <br>
	/// Direction of the search. (default = 1). <p>
	/// 
	/// -N <num> <br>
	/// Number of non improving nodes to consider before terminating search.
	/// (default = 5). <p>
	/// 
	/// -S <num> <br>
	/// Size of lookup cache for evaluated subsets. Expressed as a multiple
	/// of the number of attributes in the data set. (default = 1). <p>
	/// 
	/// </summary>
	/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.24.2.1 $
	/// </version>
	[Serializable]
	public class BestFirst:ASSearch, OptionHandler, StartSetHandler
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the current settings of BestFirst.</summary>
		/// <returns> an array of strings suitable for passing to setOptions()
		/// </returns>
		/// <summary> Parses a given list of options.
		/// 
		/// Valid options are: <p>
		/// 
		/// -P <start set> <br>
		/// Specify a starting set of attributes. Eg 1,4,7-9. <p>
		/// 
		/// -D <-1 = backward | 0 = bidirectional | 1 = forward> <br>
		/// Direction of the search. (default = 1). <p>
		/// 
		/// -N <num> <br>
		/// Number of non improving nodes to consider before terminating search.
		/// (default = 5). <p>
		/// 
		/// -S <num> <br>
		/// Size of lookup cache for evaluated subsets. Expressed as a multiple
		/// of the number of attributes in the data set. (default = 1). <p>
		/// 
		/// </summary>
		/// <param name="options">the list of options as an array of strings
		/// </param>
		/// <exception cref="Exception">if an option is not supported
		/// 
		/// 
		/// </exception>
		virtual public System.String[] Options
		{
			get
			{
				System.String[] options = new System.String[6];
				int current = 0;
				
				if (!(StartSet.Equals("")))
				{
					options[current++] = "-P";
					options[current++] = "" + startSetToString();
				}
				options[current++] = "-D";
				options[current++] = "" + m_searchDirection;
				options[current++] = "-N";
				options[current++] = "" + m_maxStale;
				
				while (current < options.Length)
				{
					options[current++] = "";
				}
				
				return options;
			}
			
			set
			{
				System.String optionString;
				resetOptions();
				
				optionString = Utils.getOption('P', value);
				if (optionString.Length != 0)
				{
					StartSet = optionString;
				}
				
				optionString = Utils.getOption('D', value);
				
				if (optionString.Length != 0)
				{
					Direction = new SelectedTag(System.Int32.Parse(optionString), TAGS_SELECTION);
				}
				else
				{
					Direction = new SelectedTag(SELECTION_FORWARD, TAGS_SELECTION);
				}
				
				optionString = Utils.getOption('N', value);
				
				if (optionString.Length != 0)
				{
					SearchTermination = System.Int32.Parse(optionString);
				}
				
				optionString = Utils.getOption('S', value);
				if (optionString.Length != 0)
				{
					LookupCacheSize = System.Int32.Parse(optionString);
				}
				
				m_debug = Utils.getFlag('Z', value);
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Return the maximum size of the evaluated subset cache (expressed as a multiplier
		/// for the number of attributes in a data set.
		/// 
		/// </summary>
		/// <returns> the maximum size of the hashtable.
		/// </returns>
		/// <summary> Set the maximum size of the evaluated subset cache (hashtable). This is
		/// expressed as a multiplier for the number of attributes in the data set.
		/// (default = 1).
		/// 
		/// </summary>
		/// <param name="size">the maximum size of the hashtable
		/// </param>
		virtual public int LookupCacheSize
		{
			get
			{
				return m_cacheSize;
			}
			
			set
			{
				if (value >= 0)
				{
					m_cacheSize = value;
				}
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Returns a list of attributes (and or attribute ranges) as a String</summary>
		/// <returns> a list of attributes (and or attribute ranges)
		/// </returns>
		/// <summary> Sets a starting set of attributes for the search. It is the
		/// search method's responsibility to report this start set (if any)
		/// in its toString() method.
		/// </summary>
		/// <param name="startSet">a string containing a list of attributes (and or ranges),
		/// eg. 1,2,6,10-15.
		/// </param>
		/// <exception cref="Exception">if start set can't be set.
		/// </exception>
		virtual public System.String StartSet
		{
			get
			{
				return m_startRange.Ranges;
			}
			
			set
			{
				m_startRange.Ranges=value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Get the termination criterion (number of non-improving nodes).
		/// 
		/// </summary>
		/// <returns> the number of non-improving nodes
		/// </returns>
		/// <summary> Set the numnber of non-improving nodes to consider before terminating
		/// search.
		/// 
		/// </summary>
		/// <param name="t">the number of non-improving nodes
		/// </param>
		/// <exception cref="Exception">if t is less than 1
		/// </exception>
		virtual public int SearchTermination
		{
			get
			{
				return m_maxStale;
			}
			
			set
			{
				if (value < 1)
				{
					throw new System.Exception("Value of -N must be > 0.");
				}
				
				m_maxStale = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Get the search direction
		/// 
		/// </summary>
		/// <returns> the direction of the search
		/// </returns>
		/// <summary> Set the search direction
		/// 
		/// </summary>
		/// <param name="d">the direction of the search
		/// </param>
		virtual public SelectedTag Direction
		{
			get
			{
				
				return new SelectedTag(m_searchDirection, TAGS_SELECTION);
			}
			
			set
			{
				
				if (value.Tags == TAGS_SELECTION)
				{
					m_searchDirection = value.getSelectedTag().ID;
				}
			}
			
		}
		
		//UPGRADE_NOTE: Field 'EnclosingInstance' was added to class 'Link2' to access its enclosing instance. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1019'"
		// Inner classes
		/// <summary> Class for a node in a linked list. Used in best first search.</summary>
		/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
		/// 
		/// </author>
		[Serializable]
		public class Link2
		{
			private void  InitBlock(BestFirst enclosingInstance)
			{
				this.enclosingInstance = enclosingInstance;
			}
			private BestFirst enclosingInstance;
			/// <summary>Get a group </summary>
			virtual public System.Object[] Data
			{
				get
				{
					return m_data;
				}
				
			}
			public BestFirst Enclosing_Instance
			{
				get
				{
					return enclosingInstance;
				}
				
			}
			
			/*    BitSet group; */
			internal System.Object[] m_data;
			internal double m_merit;
			
			
			// Constructor
			public Link2(BestFirst enclosingInstance, System.Object[] data, double mer)
			{
				InitBlock(enclosingInstance);
				//      group = (BitSet)gr.clone();
				m_data = data;
				m_merit = mer;
			}
			
			
			public override System.String ToString()
			{
				//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Object.toString' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
				return ("Node: " + m_data.ToString() + "  " + m_merit);
			}
		}
		
		
		//UPGRADE_NOTE: Field 'EnclosingInstance' was added to class 'LinkedList2' to access its enclosing instance. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1019'"
		/// <summary> Class for handling a linked list. Used in best first search.
		/// Extends the Vector class.
		/// </summary>
		/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
		/// 
		/// </author>
		public class LinkedList2:FastVector
		{
			private void  InitBlock(BestFirst enclosingInstance)
			{
				this.enclosingInstance = enclosingInstance;
			}
			private BestFirst enclosingInstance;
			public BestFirst Enclosing_Instance
			{
				get
				{
					return enclosingInstance;
				}
				
			}
			// Max number of elements in the list
			internal int m_MaxSize;
			
			// ================
			// Public methods
			// ================
			public LinkedList2(BestFirst enclosingInstance, int sz):base()
			{
				InitBlock(enclosingInstance);
				m_MaxSize = sz;
			}
			
			
			/// <summary> removes an element (Link) at a specific index from the list.</summary>
			/// <param name="index">the index of the element to be removed.
			/// 
			/// </param>
			public virtual void  removeLinkAt(int index)
			{
				if ((index >= 0) && (index < size()))
				{
					removeElementAt(index);
				}
				else
				{
					throw new System.Exception("index out of range (removeLinkAt)");
				}
			}
			
			
			/// <summary> returns the element (Link) at a specific index from the list.</summary>
			/// <param name="index">the index of the element to be returned.
			/// 
			/// </param>
			public virtual Link2 getLinkAt(int index)
			{
				if (size() == 0)
				{
					throw new System.Exception("List is empty (getLinkAt)");
				}
				else
				{
					if ((index >= 0) && (index < size()))
					{
						return ((Link2) (elementAt(index)));
					}
					else
					{
						throw new System.Exception("index out of range (getLinkAt)");
					}
				}
			}
			
			
			/// <summary> adds an element (Link) to the list.</summary>
			/// <param name="gr">the attribute set specification
			/// </param>
			/// <param name="mer">the "merit" of this attribute set
			/// 
			/// </param>
			public virtual void  addToList(System.Object[] data, double mer)
			{
				Link2 newL = new Link2(enclosingInstance, data, mer);
				
				if (size() == 0)
				{
					addElement(newL);
				}
				else
				{
					if (mer > ((Link2) (firstElement())).m_merit)
					{
						if (size() == m_MaxSize)
						{
							removeLinkAt(m_MaxSize - 1);
						}
						
						//----------
						insertElementAt(newL, 0);
					}
					else
					{
						int i = 0;
						int mysize = size();
						bool done = false;
						
						//------------
						// don't insert if list contains max elements an this
						// is worst than the last
						if ((mysize == m_MaxSize) && (mer <= ((Link2) (lastElement())).m_merit))
						{
							
						}
						//---------------
						else
						{
							while ((!done) && (i < mysize))
							{
								if (mer > ((Link2) (elementAt(i))).m_merit)
								{
									if (mysize == m_MaxSize)
									{
										removeLinkAt(m_MaxSize - 1);
									}
									
									// ---------------------
									insertElementAt(newL, i);
									done = true;
								}
								else
								{
									if (i == mysize - 1)
									{
										addElement(newL);
										done = true;
									}
									else
									{
										i++;
									}
								}
							}
						}
					}
				}
			}
		}
		
		// member variables
		/// <summary>maximum number of stale nodes before terminating search </summary>
		protected internal int m_maxStale;
		
		/// <summary>0 == backward search, 1 == forward search, 2 == bidirectional </summary>
		protected internal int m_searchDirection;
		
		/// <summary>search directions </summary>
		protected internal const int SELECTION_BACKWARD = 0;
		protected internal const int SELECTION_FORWARD = 1;
		protected internal const int SELECTION_BIDIRECTIONAL = 2;
		//UPGRADE_NOTE: Final was removed from the declaration of 'TAGS_SELECTION '. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1003'"
		public static readonly Tag[] TAGS_SELECTION = new Tag[]{new Tag(SELECTION_BACKWARD, "Backward"), new Tag(SELECTION_FORWARD, "Forward"), new Tag(SELECTION_BIDIRECTIONAL, "Bi-directional")};
		
		/// <summary>holds an array of starting attributes </summary>
		protected internal int[] m_starting;
		
		/// <summary>holds the start set for the search as a Range </summary>
		protected internal Range m_startRange;
		
		/// <summary>does the data have a class </summary>
		protected internal bool m_hasClass;
		
		/// <summary>holds the class index </summary>
		protected internal int m_classIndex;
		
		/// <summary>number of attributes in the data </summary>
		protected internal int m_numAttribs;
		
		/// <summary>total number of subsets evaluated during a search </summary>
		protected internal int m_totalEvals;
		
		/// <summary>for debugging </summary>
		protected internal bool m_debug;
		
		/// <summary>holds the merit of the best subset found </summary>
		protected internal double m_bestMerit;
		
		/// <summary>holds the maximum size of the lookup cache for evaluated subsets </summary>
		protected internal int m_cacheSize;
		
		/// <summary> Returns a string describing this search method</summary>
		/// <returns> a description of the search method suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String globalInfo()
		{
			return "BestFirst:\n\n" + "Searches the space of attribute subsets by greedy hillclimbing " + "augmented with a backtracking facility. Setting the number of " + "consecutive non-improving nodes allowed controls the level of " + "backtracking done. Best first may start with the empty set of " + "attributes and search forward, or start with the full set of " + "attributes and search backward, or start at any point and search " + "in both directions (by considering all possible single attribute " + "additions and deletions at a given point).\n";
		}
		
		/// <summary>Constructor </summary>
		public BestFirst()
		{
			resetOptions();
		}
		
		/// <summary> Returns an enumeration describing the available options.</summary>
		/// <returns> an enumeration of all the available options.
		/// 
		/// 
		/// </returns>
		public virtual System.Collections.IEnumerator listOptions()
		{
			System.Collections.ArrayList newVector = System.Collections.ArrayList.Synchronized(new System.Collections.ArrayList(4));
			
			newVector.Add(new Option("\tSpecify a starting set of attributes." + "\n\tEg. 1,3,5-7.", "P", 1, "-P <start set>"));
			newVector.Add(new Option("\tDirection of search. (default = 1).", "D", 1, "-D <0 = backward | 1 = forward " + "| 2 = bi-directional>"));
			newVector.Add(new Option("\tNumber of non-improving nodes to" + "\n\tconsider before terminating search.", "N", 1, "-N <num>"));
			newVector.Add(new Option("\tSize of lookup cache for evaluated subsets." + "\n\tExpressed as a multiple of the number of" + "\n\tattributes in the data set. (default = 1)", "S", 1, "-S <num>"));
			
			return newVector.GetEnumerator();
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String lookupCacheSizeTipText()
		{
			return "Set the maximum size of the lookup cache of evaluated subsets. This is " + "expressed as a multiplier of the number of attributes in the data set. " + "(default = 1).";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String startSetTipText()
		{
			return "Set the start point for the search. This is specified as a comma " + "seperated list off attribute indexes starting at 1. It can include " + "ranges. Eg. 1,2,5-9,17.";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String searchTerminationTipText()
		{
			return "Set the amount of backtracking. Specify the number of ";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String directionTipText()
		{
			return "Set the direction of the search.";
		}
		
		/// <summary> converts the array of starting attributes to a string. This is
		/// used by getOptions to return the actual attributes specified
		/// as the starting set. This is better than using m_startRanges.getRanges()
		/// as the same start set can be specified in different ways from the
		/// command line---eg 1,2,3 == 1-3. This is to ensure that stuff that
		/// is stored in a database is comparable.
		/// </summary>
		/// <returns> a comma seperated list of individual attribute numbers as a String
		/// </returns>
		private System.String startSetToString()
		{
			System.Text.StringBuilder FString = new System.Text.StringBuilder();
			bool didPrint;
			
			if (m_starting == null)
			{
				return StartSet;
			}
			for (int i = 0; i < m_starting.Length; i++)
			{
				didPrint = false;
				
				if ((m_hasClass == false) || (m_hasClass == true && i != m_classIndex))
				{
					FString.Append((m_starting[i] + 1));
					didPrint = true;
				}
				
				if (i == (m_starting.Length - 1))
				{
					FString.Append("");
				}
				else
				{
					if (didPrint)
					{
						FString.Append(",");
					}
				}
			}
			
			return FString.ToString();
		}
		
		/// <summary> returns a description of the search as a String</summary>
		/// <returns> a description of the search
		/// </returns>
		public override System.String ToString()
		{
			System.Text.StringBuilder BfString = new System.Text.StringBuilder();
			BfString.Append("\tBest first.\n\tStart set: ");
			
			if (m_starting == null)
			{
				BfString.Append("no attributes\n");
			}
			else
			{
				BfString.Append(startSetToString() + "\n");
			}
			
			BfString.Append("\tSearch direction: ");
			
			if (m_searchDirection == SELECTION_BACKWARD)
			{
				BfString.Append("backward\n");
			}
			else
			{
				if (m_searchDirection == SELECTION_FORWARD)
				{
					BfString.Append("forward\n");
				}
				else
				{
					BfString.Append("bi-directional\n");
				}
			}
			
			BfString.Append("\tStale search after " + m_maxStale + " node expansions\n");
			BfString.Append("\tTotal number of subsets evaluated: " + m_totalEvals + "\n");
			BfString.Append("\tMerit of best subset found: " + Utils.doubleToString(System.Math.Abs(m_bestMerit), 8, 3) + "\n");
			return BfString.ToString();
		}
		
		
		protected internal virtual void  printGroup(System.Collections.BitArray tt, int numAttribs)
		{
			int i;
			
			for (i = 0; i < numAttribs; i++)
			{
				if (tt.Get(i) == true)
				{
					System.Console.Out.Write((i + 1) + " ");
				}
			}
			
			System.Console.Out.WriteLine();
		}
		
		
		/// <summary> Searches the attribute subset space by best first search
		/// 
		/// </summary>
		/// <param name="ASEvaluator">the attribute evaluator to guide the search
		/// </param>
		/// <param name="data">the training instances.
		/// </param>
		/// <returns> an array (not necessarily ordered) of selected attribute indexes
		/// </returns>
		/// <exception cref="Exception">if the search can't be completed
		/// </exception>
		public override int[] search(ASEvaluation ASEval, Instances data)
		{
			m_totalEvals = 0;
			if (!(ASEval is SubsetEvaluator))
			{
				throw new System.Exception(ASEval.GetType().FullName + " is not a " + "Subset evaluator!");
			}
			
			if (ASEval is UnsupervisedSubsetEvaluator)
			{
				m_hasClass = false;
			}
			else
			{
				m_hasClass = true;
				m_classIndex = data.classIndex();
			}
			
			SubsetEvaluator ASEvaluator = (SubsetEvaluator) ASEval;
			m_numAttribs = data.numAttributes();
			int i, j;
			int best_size = 0;
			int size = 0;
			int done;
			int sd = m_searchDirection;
			int evals = 0;
			System.Collections.BitArray best_group, temp_group;
			int stale;
			double best_merit;
			bool ok = true;
			double merit;
			bool z;
			bool added;
			Link2 tl;
			System.Collections.Hashtable lookup = System.Collections.Hashtable.Synchronized(new System.Collections.Hashtable(m_cacheSize * m_numAttribs));
			int insertCount = 0;
			int cacheHits = 0;
			LinkedList2 bfList = new LinkedList2(this, m_maxStale);
			//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
			best_merit = - System.Double.MaxValue;
			stale = 0;
			best_group = new System.Collections.BitArray((m_numAttribs % 64 == 0?m_numAttribs / 64:m_numAttribs / 64 + 1) * 64);
			
			m_startRange.Upper=m_numAttribs - 1;
			if (!(StartSet.Equals("")))
			{
				m_starting = m_startRange.Selection;
			}
			// If a starting subset has been supplied, then initialise the bitset
			if (m_starting != null)
			{
				for (i = 0; i < m_starting.Length; i++)
				{
					if ((m_starting[i]) != m_classIndex)
					{
						//SupportClass.BitArraySupport.Set(best_group, m_starting[i]);
                        best_group.Set(m_starting[i], true);
					}
				}
				
				best_size = m_starting.Length;
				m_totalEvals++;
			}
			else
			{
				if (m_searchDirection == SELECTION_BACKWARD)
				{
					StartSet = "1-last";
					m_starting = new int[m_numAttribs];
					
					// init initial subset to all attributes
					for (i = 0, j = 0; i < m_numAttribs; i++)
					{
						if (i != m_classIndex)
						{
							//SupportClass.BitArraySupport.Set(best_group, i);
                            best_group.Set(i, true);
							m_starting[j++] = i;
						}
					}
					
					best_size = m_numAttribs - 1;
					m_totalEvals++;
				}
			}
			
			// evaluate the initial subset
			best_merit = ASEvaluator.evaluateSubset(best_group);
			// add the initial group to the list and the hash table
			System.Object[] best = new System.Object[1];
			best[0] = best_group.Clone();
			bfList.addToList(best, best_merit);
			System.Collections.BitArray tt = (System.Collections.BitArray) best_group.Clone();
            System.String hashC = tt.ToString();//SupportClass.BitArraySupport.ToString(tt);
			lookup[hashC] = "";
			
			while (stale < m_maxStale)
			{
				added = false;
				
				if (m_searchDirection == SELECTION_BIDIRECTIONAL)
				{
					// bi-directional search
					done = 2;
					sd = SELECTION_FORWARD;
				}
				else
				{
					done = 1;
				}
				
				// finished search?
				if (bfList.size() == 0)
				{
					stale = m_maxStale;
					break;
				}
				
				// copy the attribute set at the head of the list
				tl = bfList.getLinkAt(0);
				temp_group = (System.Collections.BitArray) (tl.Data[0]);
				temp_group = (System.Collections.BitArray) temp_group.Clone();
				// remove the head of the list
				bfList.removeLinkAt(0);
				// count the number of bits set (attributes)
				int kk;
				
				for (kk = 0, size = 0; kk < m_numAttribs; kk++)
				{
					if (temp_group.Get(kk))
					{
						size++;
					}
				}
				
				do 
				{
					for (i = 0; i < m_numAttribs; i++)
					{
						if (sd == SELECTION_FORWARD)
						{
							z = ((i != m_classIndex) && (!temp_group.Get(i)));
						}
						else
						{
							z = ((i != m_classIndex) && (temp_group.Get(i)));
						}
						
						if (z)
						{
							// set the bit (attribute to add/delete)
							if (sd == SELECTION_FORWARD)
							{
								//SupportClass.BitArraySupport.Set(temp_group, i);
                                temp_group.Set(i, true);
								size++;
							}
							else
							{
								temp_group.Set(i, false);
								size--;
							}
							
							/* if this subset has been seen before, then it is already 
							in the list (or has been fully expanded) */
							tt = (System.Collections.BitArray) temp_group.Clone();
                            hashC = tt.ToString();//SupportClass.BitArraySupport.ToString(tt);
							if (lookup.ContainsKey(hashC) == false)
							{
								merit = ASEvaluator.evaluateSubset(temp_group);
								m_totalEvals++;
								
								if (m_debug)
								{
									System.Console.Out.Write("Group: ");
									printGroup(tt, m_numAttribs);
									System.Console.Out.WriteLine("Merit: " + merit);
								}
								
								// is this better than the best?
								if (sd == SELECTION_FORWARD)
								{
									z = ((merit - best_merit) > 0.00001);
								}
								else
								{
									//		z = ((merit >= best_merit) && ((size) < best_size));
									if (merit == best_merit)
									{
										z = (size < best_size);
									}
									else
									{
										z = (merit > best_merit);
									}
								}
								
								if (z)
								{
									added = true;
									stale = 0;
									best_merit = merit;
									//		best_size = (size + best_size);
									best_size = size;
									best_group = (System.Collections.BitArray) (temp_group.Clone());
								}
								
								if (insertCount > m_cacheSize * m_numAttribs)
								{
									lookup = System.Collections.Hashtable.Synchronized(new System.Collections.Hashtable(m_cacheSize * m_numAttribs));
									insertCount = 0;
								}
								// insert this one in the list and in the hash table
								System.Object[] add = new System.Object[1];
								add[0] = tt.Clone();
								bfList.addToList(add, merit);
                                hashC = tt.ToString();//SupportClass.BitArraySupport.ToString(tt);
								lookup[hashC] = "";
								insertCount++;
							}
							else
							{
								cacheHits++;
							}
							
							// unset this addition(deletion)
							if (sd == SELECTION_FORWARD)
							{
								temp_group.Set(i, false);
								size--;
							}
							else
							{
								//SupportClass.BitArraySupport.Set(temp_group, i);
                                temp_group.Set(i, true);
								size++;
							}
						}
					}
					
					if (done == 2)
					{
						sd = SELECTION_BACKWARD;
					}
					
					done--;
				}
				while (done > 0);
				
				/* if we haven't added a new attribute subset then full expansion 
				of this node hasen't resulted in anything better */
				if (!added)
				{
					stale++;
				}
			}
			
			m_bestMerit = best_merit;
			return attributeList(best_group);
		}
		
		
		/// <summary> Reset options to default values</summary>
		protected internal virtual void  resetOptions()
		{
			m_maxStale = 5;
			m_searchDirection = SELECTION_FORWARD;
			m_starting = null;
			m_startRange = new Range();
			m_classIndex = - 1;
			m_totalEvals = 0;
			m_cacheSize = 1;
			m_debug = false;
		}
		
		
		/// <summary> converts a BitSet into a list of attribute indexes </summary>
		/// <param name="group">the BitSet to convert
		/// </param>
		/// <returns> an array of attribute indexes
		/// 
		/// </returns>
		protected internal virtual int[] attributeList(System.Collections.BitArray group)
		{
			int count = 0;
			
			// count how many were selected
			for (int i = 0; i < m_numAttribs; i++)
			{
				if (group.Get(i))
				{
					count++;
				}
			}
			
			int[] list = new int[count];
			count = 0;
			
			for (int i = 0; i < m_numAttribs; i++)
			{
				if (group.Get(i))
				{
					list[count++] = i;
				}
			}
			
			return list;
		}
	}
}