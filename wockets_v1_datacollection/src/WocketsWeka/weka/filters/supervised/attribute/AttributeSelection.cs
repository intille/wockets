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
*    AttributeSelection.java
*    Copyright (C) 1999 Mark Hall
*
*/
using System;
using weka.filters;
using weka.core;
using weka.attributeSelection;
namespace weka.filters.supervised.attribute
{
	
	/// <summary> Filter for doing attribute selection.<p>
	/// 
	/// Valid options are:<p>
	/// 
	/// -S <"Name of search class [search options]"> <br>
	/// Set search method for subset evaluators. <br>
	/// eg. -S "weka.attributeSelection.BestFirst -S 8" <p>
	/// 
	/// -E <"Name of attribute/subset evaluation class [evaluator options]"> <br>
	/// Set the attribute/subset evaluator. <br>
	/// eg. -E "weka.attributeSelection.CfsSubsetEval -L" <p>
	/// 
	/// </summary>
	/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.3 $
	/// </version>
	[Serializable]
	public class AttributeSelection:Filter, SupervisedFilter, OptionHandler
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the current settings for the attribute selection (search, evaluator)
		/// etc.
		/// 
		/// </summary>
		/// <returns> an array of strings suitable for passing to setOptions()
		/// </returns>
		/// <summary> Parses a given list of options. Valid options are:<p>
		/// 
		/// -S <"Name of search class [search options]"> <br>
		/// Set search method for subset evaluators. <br>
		/// eg. -S "weka.attributeSelection.BestFirst -S 8" <p>
		/// 
		/// -E <"Name of attribute/subset evaluation class [evaluator options]"> <br>
		/// Set the attribute/subset evaluator. <br>
		/// eg. -E "weka.attributeSelection.CfsSubsetEval -L" <p>
		/// 
		/// </summary>
		/// <param name="options">the list of options as an array of strings
		/// </param>
		/// <exception cref="Exception">if an option is not supported
		/// </exception>
		virtual public System.String[] Options
		{
			get
			{
				System.String[] EvaluatorOptions = new System.String[0];
				System.String[] SearchOptions = new System.String[0];
				int current = 0;
				
				if (m_ASEvaluator is OptionHandler)
				{
					EvaluatorOptions = ((OptionHandler) m_ASEvaluator).Options;
				}
				
				if (m_ASSearch is OptionHandler)
				{
					SearchOptions = ((OptionHandler) m_ASSearch).Options;
				}
				
				System.String[] setOptions = new System.String[10];
				setOptions[current++] = "-E";
				setOptions[current++] = Evaluator.GetType().FullName + " " + Utils.joinOptions(EvaluatorOptions);
				
				setOptions[current++] = "-S";
				setOptions[current++] = Search.GetType().FullName + " " + Utils.joinOptions(SearchOptions);
				
				while (current < setOptions.Length)
				{
					setOptions[current++] = "";
				}
				
				return setOptions;
			}
			
			set
			{
				
				System.String optionString;
				resetOptions();
				
				if (Utils.getFlag('X', value))
				{
					throw new System.Exception("Cross validation is not a valid option" + " when using attribute selection as a Filter.");
				}
				
				optionString = Utils.getOption('E', value);
				if (optionString.Length != 0)
				{
					optionString = optionString.Trim();
					// split a quoted evaluator name from its options (if any)
					int breakLoc = optionString.IndexOf(' ');
					System.String evalClassName = optionString;
					System.String evalOptionsString = "";
					System.String[] evalOptions = null;
					if (breakLoc != - 1)
					{
						evalClassName = optionString.Substring(0, (breakLoc) - (0));
						evalOptionsString = optionString.Substring(breakLoc).Trim();
						evalOptions = Utils.splitOptions(evalOptionsString);
					}
					Evaluator = ASEvaluation.forName(evalClassName, evalOptions);
				}
				
				if (m_ASEvaluator is AttributeEvaluator)
				{
					Search = new Ranker();
				}
				
				optionString = Utils.getOption('S', value);
				if (optionString.Length != 0)
				{
					optionString = optionString.Trim();
					int breakLoc = optionString.IndexOf(' ');
					System.String SearchClassName = optionString;
					System.String SearchOptionsString = "";
					System.String[] SearchOptions = null;
					if (breakLoc != - 1)
					{
						SearchClassName = optionString.Substring(0, (breakLoc) - (0));
						SearchOptionsString = optionString.Substring(breakLoc).Trim();
						SearchOptions = Utils.splitOptions(SearchOptionsString);
					}
					Search = ASSearch.forName(SearchClassName, SearchOptions);
				}
				
				Utils.checkForRemainingOptions(value);
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Get the name of the attribute/subset evaluator
		/// 
		/// </summary>
		/// <returns> the name of the attribute/subset evaluator as a string
		/// </returns>
		/// <summary> set a string holding the name of a attribute/subset evaluator</summary>
		virtual public ASEvaluation Evaluator
		{
			get
			{
				
				return m_ASEvaluator;
			}
			
			set
			{
				m_ASEvaluator = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Get the name of the search method
		/// 
		/// </summary>
		/// <returns> the name of the search method as a string
		/// </returns>
		/// <summary> Set as string holding the name of a search class</summary>
		virtual public ASSearch Search
		{
			get
			{
				
				return m_ASSearch;
			}
			
			set
			{
				m_ASSearch = value;
			}
			
		}
		
		/// <summary>the attribute selection evaluation object </summary>
		private weka.attributeSelection.AttributeSelection m_trainSelector;
		
		/// <summary>the attribute evaluator to use </summary>
		private ASEvaluation m_ASEvaluator;
		
		/// <summary>the search method if any </summary>
		private ASSearch m_ASSearch;
		
		/// <summary>holds a copy of the full set of valid  options passed to the filter </summary>
		private System.String[] m_FilterOptions;
		
		/// <summary>holds the selected attributes  </summary>
		private int[] m_SelectedAttributes;
		
		/// <summary> Returns a string describing this filter
		/// 
		/// </summary>
		/// <returns> a description of the filter suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String globalInfo()
		{
			
			return "A supervised attribute filter that can be used to select " + "attributes. It is very flexible and allows various search " + "and evaluation methods to be combined.";
		}
		
		/// <summary> Constructor</summary>
		public AttributeSelection()
		{
			
			resetOptions();
		}
		
		/// <summary> Returns an enumeration describing the available options.</summary>
		/// <returns> an enumeration of all the available options.
		/// </returns>
		public virtual System.Collections.IEnumerator listOptions()
		{
			
			System.Collections.ArrayList newVector = System.Collections.ArrayList.Synchronized(new System.Collections.ArrayList(6));
			
			newVector.Add(new Option("\tSets search method for subset " + "evaluators.", "S", 1, "-S <\"Name of search class" + " [search options]\">"));
			newVector.Add(new Option("\tSets attribute/subset evaluator.", "E", 1, "-E <\"Name of attribute/subset " + "evaluation class [evaluator " + "options]\">"));
			
			if ((m_ASEvaluator != null) && (m_ASEvaluator is OptionHandler))
			{
				System.Collections.IEnumerator enu = ((OptionHandler) m_ASEvaluator).listOptions();
				
				newVector.Add(new Option("", "", 0, "\nOptions specific to " + "evaluator " + m_ASEvaluator.GetType().FullName + ":"));
				//UPGRADE_TODO: Method 'java.util.Enumeration.hasMoreElements' was converted to 'System.Collections.IEnumerator.MoveNext' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationhasMoreElements'"
				while (enu.MoveNext())
				{
					//UPGRADE_TODO: Method 'java.util.Enumeration.nextElement' was converted to 'System.Collections.IEnumerator.Current' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationnextElement'"
					newVector.Add((Option) enu.Current);
				}
			}
			
			if ((m_ASSearch != null) && (m_ASSearch is OptionHandler))
			{
				System.Collections.IEnumerator enu = ((OptionHandler) m_ASSearch).listOptions();
				
				newVector.Add(new Option("", "", 0, "\nOptions specific to " + "search " + m_ASSearch.GetType().FullName + ":"));
				//UPGRADE_TODO: Method 'java.util.Enumeration.hasMoreElements' was converted to 'System.Collections.IEnumerator.MoveNext' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationhasMoreElements'"
				while (enu.MoveNext())
				{
					//UPGRADE_TODO: Method 'java.util.Enumeration.nextElement' was converted to 'System.Collections.IEnumerator.Current' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationnextElement'"
					newVector.Add((Option) enu.Current);
				}
			}
			return newVector.GetEnumerator();
		}
		
		/// <summary> Returns the tip text for this property
		/// 
		/// </summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String evaluatorTipText()
		{
			
			return "Determines how attributes/attribute subsets are evaluated.";
		}
		
		/// <summary> Returns the tip text for this property
		/// 
		/// </summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String searchTipText()
		{
			
			return "Determines the search method.";
		}
		
		/// <summary> Input an instance for filtering. Ordinarily the instance is processed
		/// and made available for output immediately. Some filters require all
		/// instances be read before producing output.
		/// 
		/// </summary>
		/// <param name="instance">the input instance
		/// </param>
		/// <returns> true if the filtered instance may now be
		/// collected with output().
		/// </returns>
		/// <exception cref="IllegalStateException">if no input format has been defined.
		/// </exception>
		/// <exception cref="Exception">if the input instance was not of the correct format 
		/// or if there was a problem with the filtering.
		/// </exception>
		public override bool input(Instance instance)
		{
			
			if (getInputFormat() == null)
			{
				throw new System.SystemException("No input instance format defined");
			}
			
			if (m_NewBatch)
			{
				resetQueue();
				m_NewBatch = false;
			}
			
			if (OutputFormatDefined)
			{
				convertInstance(instance);
				return true;
			}
			
			bufferInput(instance);
			return false;
		}
		
		/// <summary> Signify that this batch of input to the filter is finished. If the filter
		/// requires all instances prior to filtering, output() may now be called
		/// to retrieve the filtered instances.
		/// 
		/// </summary>
		/// <returns> true if there are instances pending output.
		/// </returns>
		/// <exception cref="IllegalStateException">if no input structure has been defined.
		/// </exception>
		/// <exception cref="Exception">if there is a problem during the attribute selection.
		/// </exception>
		public override bool batchFinished()
		{
			
			if (getInputFormat() == null)
			{
				throw new System.SystemException("No input instance format defined");
			}
			
			if (!OutputFormatDefined)
			{
				m_trainSelector.Evaluator = m_ASEvaluator;
				m_trainSelector.Search = m_ASSearch;
				m_trainSelector.SelectAttributes(getInputFormat());
				//      System.out.println(m_trainSelector.toResultsString());
				
				m_SelectedAttributes = m_trainSelector.selectedAttributes();
				if (m_SelectedAttributes == null)
				{
					throw new System.Exception("No selected attributes\n");
				}
				
				setOutputFormat();
				
				// Convert pending input instances
				for (int i = 0; i < getInputFormat().numInstances(); i++)
				{
					convertInstance(getInputFormat().instance(i));
				}
				flushInput();
			}
			
			m_NewBatch = true;
			return (numPendingOutput() != 0);
		}
		
		/// <summary> Set the output format. Takes the currently defined attribute set 
		/// m_InputFormat and calls setOutputFormat(Instances) appropriately.
		/// </summary>
		protected internal virtual void  setOutputFormat()
		{
			Instances informat;
			
			if (m_SelectedAttributes == null)
			{
				setOutputFormat(null);
				return ;
			}
			
			FastVector attributes = new FastVector(m_SelectedAttributes.Length);
			
			int i;
			if (m_ASEvaluator is AttributeTransformer)
			{
				informat = ((AttributeTransformer) m_ASEvaluator).transformedData();
			}
			else
			{
				informat = getInputFormat();
			}
			
			for (i = 0; i < m_SelectedAttributes.Length; i++)
			{
				attributes.addElement(informat.attribute(m_SelectedAttributes[i]).copy());
			}
			
			Instances outputFormat = new Instances(getInputFormat().relationName(), attributes, 0);
			
			
			if (!(m_ASEvaluator is UnsupervisedSubsetEvaluator) && !(m_ASEvaluator is UnsupervisedAttributeEvaluator))
			{
				outputFormat.ClassIndex = m_SelectedAttributes.Length - 1;
			}
			
			setOutputFormat(outputFormat);
		}
		
		/// <summary> Convert a single instance over. Selected attributes only are transfered.
		/// The converted instance is added to the end of
		/// the output queue.
		/// 
		/// </summary>
		/// <param name="instance">the instance to convert
		/// </param>
		protected internal virtual void  convertInstance(Instance instance)
		{
			int index = 0;
			Instance newInstance;
			double[] newVals = new double[getOutputFormat().numAttributes()];
			
			if (m_ASEvaluator is AttributeTransformer)
			{
				Instance tempInstance = ((AttributeTransformer) m_ASEvaluator).convertInstance(instance);
				for (int i = 0; i < m_SelectedAttributes.Length; i++)
				{
					int current = m_SelectedAttributes[i];
					newVals[i] = tempInstance.value_Renamed(current);
				}
			}
			else
			{
				for (int i = 0; i < m_SelectedAttributes.Length; i++)
				{
					int current = m_SelectedAttributes[i];
					newVals[i] = instance.value_Renamed(current);
				}
			}
			if (instance is SparseInstance)
			{
				push(new SparseInstance(instance.weight(), newVals));
			}
			else
			{
				push(new Instance(instance.weight(), newVals));
			}
		}
		
		/// <summary> set options to their default values</summary>
		protected internal virtual void  resetOptions()
		{
			
			m_trainSelector = new weka.attributeSelection.AttributeSelection();
			Evaluator = new CfsSubsetEval();
			Search = new BestFirst();
			m_SelectedAttributes = null;
			m_FilterOptions = null;
		}

	}
}