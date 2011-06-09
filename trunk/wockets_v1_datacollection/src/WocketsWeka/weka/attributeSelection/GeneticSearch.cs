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
*    GeneticSearch.java
*    Copyright (C) 1999 Mark Hall
*
*/
using System;
//UPGRADE_TODO: The package 'weka.core' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using weka.core;
namespace weka.attributeSelection
{
	
	/// <summary> Class for performing a genetic based search. <p>
	/// 
	/// For more information see: <p>
	/// David E. Goldberg (1989). Genetic algorithms in search, optimization and
	/// machine learning. Addison-Wesley. <p>
	/// 
	/// Valid options are: <p>
	/// 
	/// -Z <size of the population> <br>
	/// Sets the size of the population. (default = 20). <p>
	/// 
	/// -G <number of generations> <br>
	/// Sets the number of generations to perform.
	/// (default = 5). <p>
	/// 
	/// -C <probability of crossover> <br>
	/// Sets the probability that crossover will occur.
	/// (default = .6). <p>
	/// 
	/// -M <probability of mutation> <br>
	/// Sets the probability that a feature will be toggled on/off. <p>
	/// 
	/// -R <report frequency> <br>
	/// Sets how frequently reports will be generated. Eg, setting the value
	/// to 5 will generate a report every 5th generation. <p>
	/// (default = number of generations). <p>
	/// 
	/// -S <seed> <br>
	/// Sets the seed for random number generation. <p>
	/// 
	/// </summary>
	/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.14 $
	/// </version>
	[Serializable]
	public class GeneticSearch:ASSearch, StartSetHandler, OptionHandler
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the current settings of ReliefFAttributeEval.
		/// 
		/// </summary>
		/// <returns> an array of strings suitable for passing to setOptions()
		/// </returns>
		/// <summary> Parses a given list of options.
		/// 
		/// Valid options are: <p>
		/// 
		/// -Z <size of the population> <br>
		/// Sets the size of the population. (default = 20). <p>
		/// 
		/// -G <number of generations> <br>
		/// Sets the number of generations to perform.
		/// (default = 5). <p>
		/// 
		/// -C <probability of crossover> <br>
		/// Sets the probability that crossover will occur.
		/// (default = .6). <p>
		/// 
		/// -M <probability of mutation> <br>
		/// Sets the probability that a feature will be toggled on/off. <p>
		/// 
		/// -R <report frequency> <br>
		/// Sets how frequently reports will be generated. Eg, setting the value
		/// to 5 will generate a report every 5th generation. <p>
		/// (default = number of generations). <p>
		/// 
		/// -S <seed> <br>
		/// Sets the seed for random number generation. <p>
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
				System.String[] options = new System.String[14];
				int current = 0;
				
				if (!(StartSet.Equals("")))
				{
					options[current++] = "-P";
					options[current++] = "" + startSetToString();
				}
				options[current++] = "-Z";
				options[current++] = "" + PopulationSize;
				options[current++] = "-G";
				options[current++] = "" + MaxGenerations;
				options[current++] = "-C";
				options[current++] = "" + CrossoverProb;
				options[current++] = "-M";
				options[current++] = "" + MutationProb;
				options[current++] = "-R";
				options[current++] = "" + ReportFrequency;
				options[current++] = "-S";
				options[current++] = "" + Seed;
				
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
				
				optionString = Utils.getOption('Z', value);
				if (optionString.Length != 0)
				{
					PopulationSize = System.Int32.Parse(optionString);
				}
				
				optionString = Utils.getOption('G', value);
				if (optionString.Length != 0)
				{
					MaxGenerations = System.Int32.Parse(optionString);
					ReportFrequency = System.Int32.Parse(optionString);
				}
				
				optionString = Utils.getOption('C', value);
				if (optionString.Length != 0)
				{
					//UPGRADE_TODO: The differences in the format  of parameters for constructor 'java.lang.Double.Double'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
					CrossoverProb = (System.Double.Parse(optionString));
				}
				
				optionString = Utils.getOption('M', value);
				if (optionString.Length != 0)
				{
					//UPGRADE_TODO: The differences in the format  of parameters for constructor 'java.lang.Double.Double'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
					MutationProb = (System.Double.Parse(optionString));
				}
				
				optionString = Utils.getOption('R', value);
				if (optionString.Length != 0)
				{
					ReportFrequency = System.Int32.Parse(optionString);
				}
				
				optionString = Utils.getOption('S', value);
				if (optionString.Length != 0)
				{
					Seed = System.Int32.Parse(optionString);
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
				m_startRange.Ranges=value;//.setRanges(value);
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> get the value of the random number generator's seed</summary>
		/// <returns> the seed for random number generation
		/// </returns>
		/// <summary> set the seed for random number generation</summary>
		/// <param name="s">seed value
		/// </param>
		virtual public int Seed
		{
			get
			{
				return m_seed;
			}
			
			set
			{
				m_seed = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> get how often repports are generated</summary>
		/// <returns> how often reports are generated
		/// </returns>
		/// <summary> set how often reports are generated</summary>
		/// <param name="f">generate reports every f generations
		/// </param>
		virtual public int ReportFrequency
		{
			get
			{
				return m_reportFrequency;
			}
			
			set
			{
				m_reportFrequency = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> get the probability of mutation</summary>
		/// <returns> the probability of mutation occuring
		/// </returns>
		/// <summary> set the probability of mutation</summary>
		/// <param name="m">the probability for mutation occuring
		/// </param>
		virtual public double MutationProb
		{
			get
			{
				return m_pMutation;
			}
			
			set
			{
				m_pMutation = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> get the probability of crossover</summary>
		/// <returns> the probability of crossover
		/// </returns>
		/// <summary> set the probability of crossover</summary>
		/// <param name="c">the probability that two population members will exchange
		/// genetic material
		/// </param>
		virtual public double CrossoverProb
		{
			get
			{
				return m_pCrossover;
			}
			
			set
			{
				m_pCrossover = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> get the number of generations</summary>
		/// <returns> the maximum number of generations
		/// </returns>
		/// <summary> set the number of generations to evaluate</summary>
		/// <param name="m">the number of generations
		/// </param>
		virtual public int MaxGenerations
		{
			get
			{
				return m_maxGenerations;
			}
			
			set
			{
				m_maxGenerations = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> get the size of the population</summary>
		/// <returns> the population size
		/// </returns>
		/// <summary> set the population size</summary>
		/// <param name="p">the size of the population
		/// </param>
		virtual public int PopulationSize
		{
			get
			{
				return m_popSize;
			}
			
			set
			{
				m_popSize = value;
			}
			
		}
		
		/// <summary> holds a starting set as an array of attributes. Becomes one member of the
		/// initial random population
		/// </summary>
		private int[] m_starting;
		
		/// <summary>holds the start set for the search as a Range </summary>
		private Range m_startRange;
		
		/// <summary>does the data have a class </summary>
		private bool m_hasClass;
		
		/// <summary>holds the class index </summary>
		private int m_classIndex;
		
		/// <summary>number of attributes in the data </summary>
		private int m_numAttribs;
		
		/// <summary>the current population </summary>
		private GABitSet[] m_population;
		
		/// <summary>the number of individual solutions </summary>
		private int m_popSize;
		
		/// <summary>the best population member found during the search </summary>
		private GABitSet m_best;
		
		/// <summary>the number of features in the best population member </summary>
		private int m_bestFeatureCount;
		
		/// <summary>the number of entries to cache for lookup </summary>
		private int m_lookupTableSize;
		
		/// <summary>the lookup table </summary>
		private System.Collections.Hashtable m_lookupTable;
		
		/// <summary>random number generation </summary>
		private System.Random m_random;
		
		/// <summary>seed for random number generation </summary>
		private int m_seed;
		
		/// <summary>the probability of crossover occuring </summary>
		private double m_pCrossover;
		
		/// <summary>the probability of mutation occuring </summary>
		private double m_pMutation;
		
		/// <summary>sum of the current population fitness </summary>
		private double m_sumFitness;
		
		private double m_maxFitness;
		private double m_minFitness;
		private double m_avgFitness;
		
		/// <summary>the maximum number of generations to evaluate </summary>
		private int m_maxGenerations;
		
		/// <summary>how often reports are generated </summary>
		private int m_reportFrequency;
		
		/// <summary>holds the generation reports </summary>
		private System.Text.StringBuilder m_generationReports;
		
		//UPGRADE_NOTE: Field 'EnclosingInstance' was added to class 'GABitSet' to access its enclosing instance. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1019'"
		// Inner class
		[Serializable]
		protected internal class GABitSet : System.ICloneable
		{
			private void  InitBlock(GeneticSearch enclosingInstance)
			{
				this.enclosingInstance = enclosingInstance;
			}
			private GeneticSearch enclosingInstance;
			//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
			/// <summary> gets the objective merit</summary>
			/// <returns> the objective merit of this population member
			/// </returns>
			/// <summary> sets the objective merit value</summary>
			/// <param name="objective">the objective value of this population member
			/// </param>
			virtual public double Objective
			{
				get
				{
					return m_objective;
				}
				
				set
				{
					m_objective = value;
				}
				
			}
			//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
			/// <summary> gets the scaled fitness</summary>
			/// <returns> the scaled fitness of this population member
			/// </returns>
			/// <summary> sets the scaled fitness</summary>
			/// <param name="the">scaled fitness of this population member
			/// </param>
			virtual public double Fitness
			{
				get
				{
					return m_fitness;
				}
				
				set
				{
					m_fitness = value;
				}
				
			}
			//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
			/// <summary> get the chromosome</summary>
			/// <returns> the chromosome of this population member
			/// </returns>
			/// <summary> set the chromosome</summary>
			/// <param name="the">chromosome to be set for this population member
			/// </param>
			virtual public System.Collections.BitArray Chromosome
			{
				get
				{
					return m_chromosome;
				}
				
				set
				{
					m_chromosome = value;
				}
				
			}
			public GeneticSearch Enclosing_Instance
			{
				get
				{
					return enclosingInstance;
				}
				
			}
			
			private System.Collections.BitArray m_chromosome;
			
			/// <summary>holds raw merit </summary>
			//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
			private double m_objective = - System.Double.MaxValue;
			private double m_fitness;
			
			/// <summary> Constructor</summary>
			public GABitSet(GeneticSearch enclosingInstance)
			{
				InitBlock(enclosingInstance);
				m_chromosome = new System.Collections.BitArray(64);
			}
			
			/// <summary> makes a copy of this GABitSet</summary>
			/// <returns> a copy of the object
			/// </returns>
			/// <exception cref="Exception">if something goes wrong
			/// </exception>
			public virtual System.Object Clone()
			{
				GABitSet temp = new GABitSet(enclosingInstance);
				
				temp.Objective = this.Objective;
				temp.Fitness = this.Fitness;
				temp.Chromosome = (System.Collections.BitArray) (this.m_chromosome.Clone());
				return temp;
				//return super.clone();
			}
			
			/// <summary> unset a bit in the chromosome</summary>
			/// <param name="bit">the bit to be cleared
			/// </param>
			public virtual void  clear(int bit)
			{
				m_chromosome.Set(bit, false);
			}
			
			/// <summary> set a bit in the chromosome</summary>
			/// <param name="bit">the bit to be set
			/// </param>
			public virtual void  set_Renamed(int bit)
			{
				//SupportClass.BitArraySupport.Set(m_chromosome, bit);
                m_chromosome.Set(bit, true);
			}
			
			/// <summary> get the value of a bit in the chromosome</summary>
			/// <param name="bit">the bit to query
			/// </param>
			/// <returns> the value of the bit
			/// </returns>
			public virtual bool get_Renamed(int bit)
			{
				return m_chromosome.Get(bit);
			}
		}
		
		/// <summary> Returns an enumeration describing the available options.</summary>
		/// <returns> an enumeration of all the available options.
		/// 
		/// </returns>
		public virtual System.Collections.IEnumerator listOptions()
		{
			System.Collections.ArrayList newVector = System.Collections.ArrayList.Synchronized(new System.Collections.ArrayList(6));
			
			newVector.Add(new Option("\tSpecify a starting set of attributes." + "\n\tEg. 1,3,5-7." + "If supplied, the starting set becomes" + "\n\tone member of the initial random" + "\n\tpopulation.", "P", 1, "-P <start set>"));
			newVector.Add(new Option("\tSet the size of the population." + "\n\t(default = 10).", "Z", 1, "-Z <population size>"));
			newVector.Add(new Option("\tSet the number of generations." + "\n\t(default = 20)", "G", 1, "-G <number of generations>"));
			newVector.Add(new Option("\tSet the probability of crossover." + "\n\t(default = 0.6)", "C", 1, "-C <probability of" + " crossover>"));
			newVector.Add(new Option("\tSet the probability of mutation." + "\n\t(default = 0.033)", "M", 1, "-M <probability of mutation>"));
			
			newVector.Add(new Option("\tSet frequency of generation reports." + "\n\te.g, setting the value to 5 will " + "\n\t report every 5th generation" + "\n\t(default = number of generations)", "R", 1, "-R <report frequency>"));
			newVector.Add(new Option("\tSet the random number seed." + "\n\t(default = 1)", "S", 1, "-S <seed>"));
			return newVector.GetEnumerator();
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String startSetTipText()
		{
			return "Set a start point for the search. This is specified as a comma " + "seperated list off attribute indexes starting at 1. It can include " + "ranges. Eg. 1,2,5-9,17. The start set becomes one of the population " + "members of the initial population.";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String seedTipText()
		{
			return "Set the random seed.";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String reportFrequencyTipText()
		{
			return "Set how frequently reports are generated. Default is equal to " + "the number of generations meaning that a report will be printed for " + "initial and final generations. Setting the value to 5 will result in " + "a report being printed every 5 generations.";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String mutationProbTipText()
		{
			return "Set the probability of mutation occuring.";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String crossoverProbTipText()
		{
			return "Set the probability of crossover. This is the probability that " + "two population members will exchange genetic material.";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String maxGenerationsTipText()
		{
			return "Set the number of generations to evaluate.";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String populationSizeTipText()
		{
			return "Set the population size. This is the number of individuals " + "(attribute sets) in the population.";
		}
		
		/// <summary> Returns a string describing this search method</summary>
		/// <returns> a description of the search suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String globalInfo()
		{
			return "GeneticSearch :\n\nPerforms a search using the simple genetic " + "algorithm described in Goldberg (1989).\n";
		}
		
		/// <summary> Constructor. Make a new GeneticSearch object</summary>
		public GeneticSearch()
		{
			resetOptions();
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
		
		/// <summary> returns a description of the search</summary>
		/// <returns> a description of the search as a String
		/// </returns>
		public override System.String ToString()
		{
			System.Text.StringBuilder GAString = new System.Text.StringBuilder();
			GAString.Append("\tGenetic search.\n\tStart set: ");
			
			if (m_starting == null)
			{
				GAString.Append("no attributes\n");
			}
			else
			{
				GAString.Append(startSetToString() + "\n");
			}
			GAString.Append("\tPopulation size: " + m_popSize);
			GAString.Append("\n\tNumber of generations: " + m_maxGenerations);
			GAString.Append("\n\tProbability of crossover: " + Utils.doubleToString(m_pCrossover, 6, 3));
			GAString.Append("\n\tProbability of mutation: " + Utils.doubleToString(m_pMutation, 6, 3));
			GAString.Append("\n\tReport frequency: " + m_reportFrequency);
			GAString.Append("\n\tRandom number seed: " + m_seed + "\n");
			GAString.Append(m_generationReports.ToString());
			return GAString.ToString();
		}
		
		/// <summary> Searches the attribute subset space using a genetic algorithm.
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
			
			m_best = null;
			m_generationReports = new System.Text.StringBuilder();
			
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
			
			m_startRange.Upper=m_numAttribs - 1;
			if (!(StartSet.Equals("")))
			{
				m_starting = m_startRange.Selection;//.getSelection();
			}
			
			// initial random population
			m_lookupTable = System.Collections.Hashtable.Synchronized(new System.Collections.Hashtable(m_lookupTableSize));
			//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.util.Random.Random'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
			m_random = new System.Random((System.Int32) m_seed);
			m_population = new GABitSet[m_popSize];
			
			// set up random initial population
			initPopulation();
			evaluatePopulation(ASEvaluator);
			populationStatistics();
			scalePopulation();
			checkBest();
			m_generationReports.Append(populationReport(0));
			
			bool converged;
			for (int i = 1; i <= m_maxGenerations; i++)
			{
				generation();
				evaluatePopulation(ASEvaluator);
				populationStatistics();
				scalePopulation();
				// find the best pop member and check for convergence
				converged = checkBest();
				
				if ((i == m_maxGenerations) || ((i % m_reportFrequency) == 0) || (converged == true))
				{
					m_generationReports.Append(populationReport(i));
					if (converged == true)
					{
						break;
					}
				}
			}
			return attributeList(m_best.Chromosome);
		}
		
		/// <summary> converts a BitSet into a list of attribute indexes </summary>
		/// <param name="group">the BitSet to convert
		/// </param>
		/// <returns> an array of attribute indexes
		/// 
		/// </returns>
		private int[] attributeList(System.Collections.BitArray group)
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
		
		/// <summary> checks to see if any population members in the current
		/// population are better than the best found so far. Also checks
		/// to see if the search has converged---that is there is no difference
		/// in fitness between the best and worse population member
		/// </summary>
		/// <returns> true is the search has converged
		/// </returns>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		private bool checkBest()
		{
			int i, j, count, lowestCount = m_numAttribs;
			//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
			double b = - System.Double.MaxValue;
			GABitSet localbest = null;
			System.Collections.BitArray temp;
			bool converged = false;
			int oldcount = System.Int32.MaxValue;
			
			if (m_maxFitness - m_minFitness > 0)
			{
				// find the best in this population
				for (i = 0; i < m_popSize; i++)
				{
					if (m_population[i].Objective > b)
					{
						b = m_population[i].Objective;
						localbest = m_population[i];
						oldcount = countFeatures(localbest.Chromosome);
					}
					else if (Utils.eq(m_population[i].Objective, b))
					{
						// see if it contains fewer features
						count = countFeatures(m_population[i].Chromosome);
						if (count < oldcount)
						{
							b = m_population[i].Objective;
							localbest = m_population[i];
							oldcount = count;
						}
					}
				}
			}
			else
			{
				// look for the smallest subset
				for (i = 0; i < m_popSize; i++)
				{
					temp = m_population[i].Chromosome;
					count = countFeatures(temp); ;
					
					if (count < lowestCount)
					{
						lowestCount = count;
						localbest = m_population[i];
						b = localbest.Objective;
					}
				}
				converged = true;
			}
			
			// count the number of features in localbest
			count = 0;
			temp = localbest.Chromosome;
			count = countFeatures(temp);
			
			// compare to the best found so far
			if (m_best == null)
			{
				m_best = (GABitSet) localbest.Clone();
				m_bestFeatureCount = count;
			}
			else if (b > m_best.Objective)
			{
				m_best = (GABitSet) localbest.Clone();
				m_bestFeatureCount = count;
			}
			else if (Utils.eq(m_best.Objective, b))
			{
				// see if the localbest has fewer features than the best so far
				if (count < m_bestFeatureCount)
				{
					m_best = (GABitSet) localbest.Clone();
					m_bestFeatureCount = count;
				}
			}
			return converged;
		}
		
		/// <summary> counts the number of features in a subset</summary>
		/// <param name="featureSet">the feature set for which to count the features
		/// </param>
		/// <returns> the number of features in the subset
		/// </returns>
		private int countFeatures(System.Collections.BitArray featureSet)
		{
			int count = 0;
			for (int i = 0; i < m_numAttribs; i++)
			{
				if (featureSet.Get(i))
				{
					count++;
				}
			}
			return count;
		}
		
		/// <summary> performs a single generation---selection, crossover, and mutation</summary>
		/// <exception cref="Exception">if an error occurs
		/// </exception>
		private void  generation()
		{
			int i, j = 0;
			//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
			double best_fit = - System.Double.MaxValue;
			int old_count = 0;
			int count;
			GABitSet[] newPop = new GABitSet[m_popSize];
			int parent1, parent2;
			
			/** first ensure that the population best is propogated into the new
			generation */
			for (i = 0; i < m_popSize; i++)
			{
				if (m_population[i].Fitness > best_fit)
				{
					j = i;
					best_fit = m_population[i].Fitness;
					old_count = countFeatures(m_population[i].Chromosome);
				}
				else if (Utils.eq(m_population[i].Fitness, best_fit))
				{
					count = countFeatures(m_population[i].Chromosome);
					if (count < old_count)
					{
						j = i;
						best_fit = m_population[i].Fitness;
						old_count = count;
					}
				}
			}
			newPop[0] = (GABitSet) (m_population[j].Clone());
			newPop[1] = newPop[0];
			
			for (j = 2; j < m_popSize; j += 2)
			{
				parent1 = select();
				parent2 = select();
				newPop[j] = (GABitSet) (m_population[parent1].Clone());
				newPop[j + 1] = (GABitSet) (m_population[parent2].Clone());
				// if parents are equal mutate one bit
				if (parent1 == parent2)
				{
					int r;
					if (m_hasClass)
					{
						//UPGRADE_TODO: Method 'java.util.Random.nextInt' was converted to 'System.Random.Next' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073'"
						while ((r = (System.Math.Abs(m_random.Next()) % m_numAttribs)) == m_classIndex)
							;
					}
					else
					{
						//UPGRADE_TODO: Method 'java.util.Random.nextInt' was converted to 'System.Random.Next' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073'"
						r = m_random.Next() % m_numAttribs;
					}
					
					if (newPop[j].get_Renamed(r))
					{
						newPop[j].clear(r);
					}
					else
					{
						newPop[j].set_Renamed(r);
					}
				}
				else
				{
					// crossover
					double r = m_random.NextDouble();
					if (m_numAttribs >= 3)
					{
						if (r < m_pCrossover)
						{
							// cross point
							//UPGRADE_TODO: Method 'java.util.Random.nextInt' was converted to 'System.Random.Next' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073'"
							int cp = System.Math.Abs(m_random.Next());
							
							cp %= (m_numAttribs - 2);
							cp++;
							
							for (i = 0; i < cp; i++)
							{
								if (m_population[parent1].get_Renamed(i))
								{
									newPop[j + 1].set_Renamed(i);
								}
								else
								{
									newPop[j + 1].clear(i);
								}
								if (m_population[parent2].get_Renamed(i))
								{
									newPop[j].set_Renamed(i);
								}
								else
								{
									newPop[j].clear(i);
								}
							}
						}
					}
					
					// mutate
					for (int k = 0; k < 2; k++)
					{
						for (i = 0; i < m_numAttribs; i++)
						{
							r = m_random.NextDouble();
							if (r < m_pMutation)
							{
								if (m_hasClass && (i == m_classIndex))
								{
									// ignore class attribute
								}
								else
								{
									if (newPop[j + k].get_Renamed(i))
									{
										newPop[j + k].clear(i);
									}
									else
									{
										newPop[j + k].set_Renamed(i);
									}
								}
							}
						}
					}
				}
			}
			
			m_population = newPop;
		}
		
		/// <summary> selects a population member to be considered for crossover</summary>
		/// <returns> the index of the selected population member
		/// </returns>
		private int select()
		{
			int i;
			double r, partsum;
			
			partsum = 0;
			r = m_random.NextDouble() * m_sumFitness;
			for (i = 0; i < m_popSize; i++)
			{
				partsum += m_population[i].Fitness;
				if (partsum >= r)
				{
					break;
				}
			}
			return i;
		}
		
		/// <summary> evaluates an entire population. Population members are looked up in
		/// a hash table and if they are not found then they are evaluated using
		/// ASEvaluator.
		/// </summary>
		/// <param name="ASEvaluator">the subset evaluator to use for evaluating population
		/// members
		/// </param>
		/// <exception cref="Exception">if something goes wrong during evaluation
		/// </exception>
		private void  evaluatePopulation(SubsetEvaluator ASEvaluator)
		{
			int i;
			double merit;
			
			for (i = 0; i < m_popSize; i++)
			{
				// if its not in the lookup table then evaluate and insert
				if (m_lookupTable.ContainsKey(m_population[i].Chromosome) == false)
				{
					merit = ASEvaluator.evaluateSubset(m_population[i].Chromosome);
					m_population[i].Objective = merit;
					m_lookupTable[m_population[i].Chromosome] = m_population[i];
				}
				else
				{
					GABitSet temp = (GABitSet) m_lookupTable[m_population[i].Chromosome];
					m_population[i].Objective = temp.Objective;
				}
			}
		}
		
		/// <summary> creates random population members for the initial population. Also
		/// sets the first population member to be a start set (if any) 
		/// provided by the user
		/// </summary>
		/// <exception cref="Exception">if the population can't be created
		/// </exception>
		private void  initPopulation()
		{
			int i, j, bit;
			int num_bits;
			bool ok;
			int start = 0;
			
			// add the start set as the first population member (if specified)
			if (m_starting != null)
			{
				m_population[0] = new GABitSet(this);
				for (i = 0; i < m_starting.Length; i++)
				{
					if ((m_starting[i]) != m_classIndex)
					{
						m_population[0].set_Renamed(m_starting[i]);
					}
				}
				start = 1;
			}
			
			for (i = start; i < m_popSize; i++)
			{
				m_population[i] = new GABitSet(this);
				
				//UPGRADE_TODO: Method 'java.util.Random.nextInt' was converted to 'System.Random.Next' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073'"
				num_bits = m_random.Next();
				num_bits = num_bits % m_numAttribs - 1;
				if (num_bits < 0)
				{
					num_bits *= (- 1);
				}
				if (num_bits == 0)
				{
					num_bits = 1;
				}
				
				for (j = 0; j < num_bits; j++)
				{
					ok = false;
					do 
					{
						//UPGRADE_TODO: Method 'java.util.Random.nextInt' was converted to 'System.Random.Next' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073'"
						bit = m_random.Next();
						if (bit < 0)
						{
							bit *= (- 1);
						}
						bit = bit % m_numAttribs;
						if (m_hasClass)
						{
							if (bit != m_classIndex)
							{
								ok = true;
							}
						}
						else
						{
							ok = true;
						}
					}
					while (!ok);
					
					if (bit > m_numAttribs)
					{
						throw new System.Exception("Problem in population init");
					}
					m_population[i].set_Renamed(bit);
				}
			}
		}
		
		/// <summary> calculates summary statistics for the current population</summary>
		private void  populationStatistics()
		{
			int i;
			
			m_sumFitness = m_minFitness = m_maxFitness = m_population[0].Objective;
			
			for (i = 1; i < m_popSize; i++)
			{
				m_sumFitness += m_population[i].Objective;
				if (m_population[i].Objective > m_maxFitness)
				{
					m_maxFitness = m_population[i].Objective;
				}
				else if (m_population[i].Objective < m_minFitness)
				{
					m_minFitness = m_population[i].Objective;
				}
			}
			m_avgFitness = (m_sumFitness / m_popSize);
		}
		
		/// <summary> scales the raw (objective) merit of the population members</summary>
		private void  scalePopulation()
		{
			int j;
			double a = 0;
			double b = 0;
			double fmultiple = 2.0;
			double delta;
			
			// prescale
			if (m_minFitness > ((fmultiple * m_avgFitness - m_maxFitness) / (fmultiple - 1.0)))
			{
				delta = m_maxFitness - m_avgFitness;
				a = ((fmultiple - 1.0) * m_avgFitness / delta);
				b = m_avgFitness * (m_maxFitness - fmultiple * m_avgFitness) / delta;
			}
			else
			{
				delta = m_avgFitness - m_minFitness;
				a = m_avgFitness / delta;
				b = (- m_minFitness) * m_avgFitness / delta;
			}
			
			// scalepop
			m_sumFitness = 0;
			for (j = 0; j < m_popSize; j++)
			{
				if (a == System.Double.PositiveInfinity || a == System.Double.NegativeInfinity || b == System.Double.PositiveInfinity || b == System.Double.NegativeInfinity)
				{
					m_population[j].Fitness = m_population[j].Objective;
				}
				else
				{
					m_population[j].Fitness = System.Math.Abs((a * m_population[j].Objective + b));
				}
				m_sumFitness += m_population[j].Fitness;
			}
		}
		
		/// <summary> generates a report on the current population</summary>
		/// <returns> a report as a String
		/// </returns>
		private System.String populationReport(int genNum)
		{
			int i;
			System.Text.StringBuilder temp = new System.Text.StringBuilder();
			
			if (genNum == 0)
			{
				temp.Append("\nInitial population\n");
			}
			else
			{
				temp.Append("\nGeneration: " + genNum + "\n");
			}
			temp.Append("merit   \tscaled  \tsubset\n");
			
			for (i = 0; i < m_popSize; i++)
			{
				temp.Append(Utils.doubleToString(System.Math.Abs(m_population[i].Objective), 8, 5) + "\t" + Utils.doubleToString(m_population[i].Fitness, 8, 5) + "\t");
				
				temp.Append(printPopMember(m_population[i].Chromosome) + "\n");
			}
			return temp.ToString();
		}
		
		/// <summary> prints a population member as a series of attribute numbers</summary>
		/// <param name="temp">the chromosome of a population member
		/// </param>
		/// <returns> a population member as a String of attribute numbers
		/// </returns>
		private System.String printPopMember(System.Collections.BitArray temp)
		{
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			
			for (int j = 0; j < m_numAttribs; j++)
			{
				if (temp.Get(j))
				{
					text.Append((j + 1) + " ");
				}
			}
			return text.ToString();
		}
		
		/// <summary> prints a population member's chromosome</summary>
		/// <param name="temp">the chromosome of a population member
		/// </param>
		/// <returns> a population member's chromosome as a String
		/// </returns>
		private System.String printPopChrom(System.Collections.BitArray temp)
		{
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			
			for (int j = 0; j < m_numAttribs; j++)
			{
				if (temp.Get(j))
				{
					text.Append("1");
				}
				else
				{
					text.Append("0");
				}
			}
			return text.ToString();
		}
		
		/// <summary> reset to default values for options</summary>
		private void  resetOptions()
		{
			m_population = null;
			m_popSize = 20;
			m_lookupTableSize = 1001;
			m_pCrossover = 0.6;
			m_pMutation = 0.033;
			m_maxGenerations = 20;
			m_reportFrequency = m_maxGenerations;
			m_starting = null;
			m_startRange = new Range();
			m_seed = 1;
		}
	}
}