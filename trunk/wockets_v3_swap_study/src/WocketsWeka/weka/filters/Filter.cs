/*
*    Filter.java
*    Copyright (C) 1999 Len Trigg
*
*/
using System;
using Attribute = weka.core.Attribute;
using Instance = weka.core.Instance;
using Instances = weka.core.Instances;
using Option = weka.core.Option;
//UPGRADE_TODO: The type 'weka.core.Queue' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using Queue = weka.core.Queue;
using Utils = weka.core.Utils;
namespace weka.filters
{
	
	/// <summary> An abstract class for instance filters: objects that take instances
	/// as input, carry out some transformation on the instance and then
	/// output the instance. The method implementations in this class
	/// assume that most of the work will be done in the methods overridden
	/// by subclasses.<p>
	/// 
	/// A simple example of filter use. This example doesn't remove
	/// instances from the output queue until all instances have been
	/// input, so has higher memory consumption than an approach that
	/// uses output instances as they are made available:<p>
	/// 
	/// <code> <pre>
	/// Filter filter = ..some type of filter..
	/// Instances instances = ..some instances..
	/// for (int i = 0; i < data.numInstances(); i++) {
	/// filter.input(data.instance(i));
	/// }
	/// filter.batchFinished();
	/// Instances newData = filter.outputFormat();
	/// Instance processed;
	/// while ((processed = filter.output()) != null) {
	/// newData.add(processed);
	/// }
	/// ..do something with newData..
	/// </pre> </code>
	/// 
	/// </summary>
	/// <author>  Len Trigg (trigg@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.24.2.1 $
	/// </version>
	/// <attribute>  System.ComponentModel.CategoryAttribute("Filters")  </attribute>
#if !PocketPC
    [Serializable]
#endif
	public abstract class Filter
	{
		/// <summary> Returns an array containing the indices of all string attributes in the
		/// input format. This index is created during setInputFormat()
		/// 
		/// </summary>
		/// <returns> an array containing the indices of string attributes in the 
		/// input dataset.
		/// </returns>
		virtual protected internal int[] InputStringIndex
		{
			get
			{
				
				return m_InputStringAtts;
			}
			
		}
		/// <summary> Returns an array containing the indices of all string attributes in the
		/// output format. This index is created during setOutputFormat()
		/// 
		/// </summary>
		/// <returns> an array containing the indices of string attributes in the 
		/// output dataset.
		/// </returns>
		virtual protected internal int[] OutputStringIndex
		{
			get
			{
				
				return m_OutputStringAtts;
			}
			
		}
		/// <summary> Returns whether the output format is ready to be collected
		/// 
		/// </summary>
		/// <returns> true if the output format is set
		/// </returns>
		virtual public bool OutputFormatDefined
		{
			get
			{
				
				return (m_OutputFormat != null);
			}
			
		}
		/*
		* Filter refactoring TODO:
		*
		* - Update all filters to use getOutputFormat and setInputFormat
		* instead of outputFormat, outputFormatPeek and inputFormat.
		* - Update users of filters to use getOutputFormat and setInputFormat
		* - remove outputFormat, outputFormatPeek and inputFormat
		*
		*/
		
		/// <summary>Debugging mode </summary>
		private bool m_Debug = false;
		/// <summary>The output format for instances </summary>
		private Instances m_OutputFormat = null;
		/// <summary>The output instance queue </summary>
		private Queue m_OutputQueue = null;
		/// <summary>Indices of string attributes in the output format </summary>
		private int[] m_OutputStringAtts = null;
		/// <summary>Indices of string attributes in the input format </summary>
		private int[] m_InputStringAtts = null;
		/// <summary>The input format for instances </summary>
		private Instances m_InputFormat = null;
		/// <summary>Record whether the filter is at the start of a batch </summary>
		protected internal bool m_NewBatch = true;
		/// <summary>True if the first batch has been done </summary>
		protected internal bool m_FirstBatchDone = false;
		
		
		/// <summary> Sets the format of output instances. The derived class should use this
		/// method once it has determined the outputformat. The 
		/// output queue is cleared.
		/// 
		/// </summary>
		/// <param name="outputFormat">the new output format
		/// </param>
		protected internal virtual void  setOutputFormat(Instances outputFormat)
		{
			if (outputFormat != null)
			{
				m_OutputFormat = outputFormat.stringFreeStructure();
				m_OutputStringAtts = getStringIndices(m_OutputFormat);
				
				// Rename the attribute
				System.String relationName = outputFormat.relationName() + "-" + this.GetType().FullName;
				//			if (this instanceof OptionHandler) 
				//			{
				//				String [] options = ((OptionHandler)this).getOptions();
				//				for (int i = 0; i < options.length; i++) 
				//				{
				//					relationName += options[i].trim();
				//				}
				//			}
				m_OutputFormat.RelationName = relationName;
			}
			else
			{
				m_OutputFormat = null;
			}
			m_OutputQueue = new Queue();
		}
		
		/// <summary> Gets the currently set inputformat instances. This dataset may contain
		/// buffered instances.
		/// 
		/// </summary>
		/// <returns> the input Instances.
		/// </returns>
		protected internal virtual Instances getInputFormat()
		{
			
			return m_InputFormat;
		}
		
		/// <summary> Returns a reference to the current input format without
		/// copying it.
		/// 
		/// </summary>
		/// <returns> a reference to the current input format
		/// </returns>
		protected internal virtual Instances inputFormatPeek()
		{
			
			return m_InputFormat;
		}
		
		/// <summary> Returns a reference to the current output format without
		/// copying it.
		/// 
		/// </summary>
		/// <returns> a reference to the current output format
		/// </returns>
		protected internal virtual Instances outputFormatPeek()
		{
			
			return m_OutputFormat;
		}
		
		/// <summary> Adds an output instance to the queue. The derived class should use this
		/// method for each output instance it makes available. 
		/// 
		/// </summary>
		/// <param name="instance">the instance to be added to the queue.
		/// </param>
		protected internal virtual void  push(Instance instance)
		{
			
			if (instance != null)
			{
				copyStringValues(instance, m_OutputFormat, m_OutputStringAtts);
				instance.Dataset = m_OutputFormat;
				m_OutputQueue.push(instance);
			}
		}
		
		/// <summary> Clears the output queue.</summary>
		protected internal virtual void  resetQueue()
		{
			
			m_OutputQueue = new Queue();
		}
		
		/// <summary> Adds the supplied input instance to the inputformat dataset for
		/// later processing.  Use this method rather than
		/// getInputFormat().add(instance). Or else. Note that the provided
		/// instance gets copied when buffered. 
		/// 
		/// </summary>
		/// <param name="instance">the <code>Instance</code> to buffer.  
		/// </param>
		protected internal virtual void  bufferInput(Instance instance)
		{
			
			if (instance != null)
			{
				copyStringValues(instance, m_InputFormat, m_InputStringAtts);
				m_InputFormat.add(instance);
			}
		}
		
		/// <summary> Copies string values contained in the instance copied to a new
		/// dataset. The Instance must already be assigned to a dataset. This
		/// dataset and the destination dataset must have the same structure.
		/// 
		/// </summary>
		/// <param name="instance">the Instance containing the string values to copy.
		/// </param>
		/// <param name="destDataset">the destination set of Instances
		/// </param>
		/// <param name="strAtts">an array containing the indices of any string attributes
		/// in the dataset.  
		/// </param>
		private void  copyStringValues(Instance inst, Instances destDataset, int[] strAtts)
		{
			
			if (strAtts.Length == 0)
			{
				return ;
			}
			if (inst.dataset() == null)
			{
				throw new System.ArgumentException("Instance has no dataset assigned!!");
			}
			else if (inst.dataset().numAttributes() != destDataset.numAttributes())
			{
				throw new System.ArgumentException("Src and Dest differ in # of attributes!!");
			}
			copyStringValues(inst, true, inst.dataset(), strAtts, destDataset, strAtts);
		}
		
		/// <summary> Takes string values referenced by an Instance and copies them from a
		/// source dataset to a destination dataset. The instance references are
		/// updated to be valid for the destination dataset. The instance may have the 
		/// structure (i.e. number and attribute position) of either dataset (this
		/// affects where references are obtained from). The source dataset must
		/// have the same structure as the filter input format and the destination
		/// must have the same structure as the filter output format.
		/// 
		/// </summary>
		/// <param name="instance">the instance containing references to strings in the source
		/// dataset that will have references updated to be valid for the destination
		/// dataset.
		/// </param>
		/// <param name="instSrcCompat">true if the instance structure is the same as the
		/// source, or false if it is the same as the destination
		/// </param>
		/// <param name="srcDataset">the dataset for which the current instance string
		/// references are valid (after any position mapping if needed)
		/// </param>
		/// <param name="destDataset">the dataset for which the current instance string
		/// references need to be inserted (after any position mapping if needed)
		/// </param>
		protected internal virtual void  copyStringValues(Instance instance, bool instSrcCompat, Instances srcDataset, Instances destDataset)
		{
			
			copyStringValues(instance, instSrcCompat, srcDataset, m_InputStringAtts, destDataset, m_OutputStringAtts);
		}
		
		/// <summary> Takes string values referenced by an Instance and copies them from a
		/// source dataset to a destination dataset. The instance references are
		/// updated to be valid for the destination dataset. The instance may have the 
		/// structure (i.e. number and attribute position) of either dataset (this
		/// affects where references are obtained from). Only works if the number
		/// of string attributes is the same in both indices (implicitly these string
		/// attributes should be semantically same but just with shifted positions).
		/// 
		/// </summary>
		/// <param name="instance">the instance containing references to strings in the source
		/// dataset that will have references updated to be valid for the destination
		/// dataset.
		/// </param>
		/// <param name="instSrcCompat">true if the instance structure is the same as the
		/// source, or false if it is the same as the destination (i.e. which of the
		/// string attribute indices contains the correct locations for this instance).
		/// </param>
		/// <param name="srcDataset">the dataset for which the current instance string
		/// references are valid (after any position mapping if needed)
		/// </param>
		/// <param name="srcStrAtts">an array containing the indices of string attributes
		/// in the source datset.
		/// </param>
		/// <param name="destDataset">the dataset for which the current instance string
		/// references need to be inserted (after any position mapping if needed)
		/// </param>
		/// <param name="destStrAtts">an array containing the indices of string attributes
		/// in the destination datset.
		/// </param>
		protected internal virtual void  copyStringValues(Instance instance, bool instSrcCompat, Instances srcDataset, int[] srcStrAtts, Instances destDataset, int[] destStrAtts)
		{
			if (srcDataset == destDataset)
			{
				return ;
			}
			if (srcStrAtts.Length != destStrAtts.Length)
			{
				throw new System.ArgumentException("Src and Dest string indices differ in length!!");
			}
			for (int i = 0; i < srcStrAtts.Length; i++)
			{
				int instIndex = instSrcCompat?srcStrAtts[i]:destStrAtts[i];
				Attribute src = srcDataset.attribute(srcStrAtts[i]);
				Attribute dest = destDataset.attribute(destStrAtts[i]);
				if (!instance.isMissing(instIndex))
				{
					//System.err.println(instance.value(srcIndex) 
					//                   + " " + src.numValues()
					//                   + " " + dest.numValues());
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					int valIndex = dest.addStringValue(src, (int) instance.value_Renamed(instIndex));
					// setValue here shouldn't be too slow here unless your dataset has
					// squillions of string attributes
					instance.setValue(instIndex, (double) valIndex);
				}
			}
		}
		
		/// <summary> This will remove all buffered instances from the inputformat dataset.
		/// Use this method rather than getInputFormat().delete();
		/// </summary>
		protected internal virtual void  flushInput()
		{
			
			if (m_InputStringAtts.Length > 0)
			{
				m_InputFormat = m_InputFormat.stringFreeStructure();
			}
			else
			{
				// This more efficient than new Instances(m_InputFormat, 0);
				m_InputFormat.delete();
			}
		}
		
		/// <deprecated> use <code>setInputFormat(Instances)</code> instead.
		/// </deprecated>
		public virtual bool inputFormat(Instances instanceInfo)
		{
			
			return setInputFormat(instanceInfo);
		}
		
		/// <summary> Sets the format of the input instances. If the filter is able to
		/// determine the output format before seeing any input instances, it
		/// does so here. This default implementation clears the output format
		/// and output queue, and the new batch flag is set. Overriders should
		/// call <code>super.setInputFormat(Instances)</code>
		/// 
		/// </summary>
		/// <param name="instanceInfo">an Instances object containing the input instance
		/// structure (any instances contained in the object are ignored - only the
		/// structure is required).
		/// </param>
		/// <returns> true if the outputFormat may be collected immediately
		/// </returns>
		/// <exception cref="Exception">if the inputFormat can't be set successfully 
		/// </exception>
		public virtual bool setInputFormat(Instances instanceInfo)
		{
			
			m_InputFormat = instanceInfo.stringFreeStructure();
			m_InputStringAtts = getStringIndices(instanceInfo);
			m_OutputFormat = null;
			m_OutputQueue = new Queue();
			m_NewBatch = true;
			m_FirstBatchDone = false;
			return false;
		}
		
		/// <deprecated> use <code>getOutputFormat()</code> instead.
		/// </deprecated>
		public virtual Instances outputFormat()
		{
			
			return getOutputFormat();
		}
		
		/// <summary> Gets the format of the output instances. This should only be called
		/// after input() or batchFinished() has returned true. The relation
		/// name of the output instances should be changed to reflect the
		/// action of the filter (eg: add the filter name and options).
		/// 
		/// </summary>
		/// <returns> an Instances object containing the output instance
		/// structure only.
		/// </returns>
		/// <exception cref="NullPointerException">if no input structure has been
		/// defined (or the output format hasn't been determined yet) 
		/// </exception>
		public virtual Instances getOutputFormat()
		{
			
			if (m_OutputFormat == null)
			{
				throw new System.NullReferenceException("No output format defined.");
			}
			return new Instances(m_OutputFormat, 0);
		}
		
		/// <summary> Input an instance for filtering. Ordinarily the instance is
		/// processed and made available for output immediately. Some filters
		/// require all instances be read before producing output, in which
		/// case output instances should be collected after calling
		/// batchFinished(). If the input marks the start of a new batch, the
		/// output queue is cleared. This default implementation assumes all
		/// instance conversion will occur when batchFinished() is called.
		/// 
		/// </summary>
		/// <param name="instance">the input instance
		/// </param>
		/// <returns> true if the filtered instance may now be
		/// collected with output().
		/// </returns>
		/// <exception cref="NullPointerException">if the input format has not been
		/// defined.
		/// </exception>
		/// <exception cref="Exception">if the input instance was not of the correct 
		/// format or if there was a problem with the filtering.  
		/// </exception>
		public virtual bool input(Instance instance)
		{
			
			if (m_InputFormat == null)
			{
				throw new System.NullReferenceException("No input instance format defined");
			}
			if (m_NewBatch)
			{
				m_OutputQueue = new Queue();
				m_NewBatch = false;
			}
			bufferInput(instance);
			return false;
		}
		
		/// <summary> Signify that this batch of input to the filter is finished. If
		/// the filter requires all instances prior to filtering, output()
		/// may now be called to retrieve the filtered instances. Any
		/// subsequent instances filtered should be filtered based on setting
		/// obtained from the first batch (unless the inputFormat has been
		/// re-assigned or new options have been set). This default
		/// implementation assumes all instance processing occurs during
		/// inputFormat() and input().
		/// 
		/// </summary>
		/// <returns> true if there are instances pending output
		/// </returns>
		/// <exception cref="NullPointerException">if no input structure has been defined,
		/// </exception>
		/// <exception cref="Exception">if there was a problem finishing the batch.
		/// </exception>
		public virtual bool batchFinished()
		{
			
			if (m_InputFormat == null)
			{
				throw new System.NullReferenceException("No input instance format defined");
			}
			flushInput();
			m_NewBatch = true;
			m_FirstBatchDone = true;
			return (numPendingOutput() != 0);
		}
		
		
		/// <summary> Output an instance after filtering and remove from the output queue.
		/// 
		/// </summary>
		/// <returns> the instance that has most recently been filtered (or null if
		/// the queue is empty).
		/// </returns>
		/// <exception cref="NullPointerException">if no output structure has been defined
		/// </exception>
		public virtual Instance output()
		{
			
			if (m_OutputFormat == null)
			{
				throw new System.NullReferenceException("No output instance format defined");
			}
			if (m_OutputQueue.empty())
			{
				return null;
			}
			Instance result = (Instance) m_OutputQueue.pop();
			// Clear out references to old strings occasionally
			if (m_OutputQueue.empty() && m_NewBatch)
			{
				if (m_OutputStringAtts.Length > 0)
				{
					m_OutputFormat = m_OutputFormat.stringFreeStructure();
				}
			}
			return result;
		}
		
		/// <summary> Output an instance after filtering but do not remove from the
		/// output queue.
		/// 
		/// </summary>
		/// <returns> the instance that has most recently been filtered (or null if
		/// the queue is empty).
		/// </returns>
		/// <exception cref="NullPointerException">if no input structure has been defined 
		/// </exception>
		public virtual Instance outputPeek()
		{
			
			if (m_OutputFormat == null)
			{
				throw new System.NullReferenceException("No output instance format defined");
			}
			if (m_OutputQueue.empty())
			{
				return null;
			}
			Instance result = (Instance) m_OutputQueue.peek();
			return result;
		}
		
		/// <summary> Returns the number of instances pending output
		/// 
		/// </summary>
		/// <returns> the number of instances  pending output
		/// </returns>
		/// <exception cref="NullPointerException">if no input structure has been defined
		/// </exception>
		public virtual int numPendingOutput()
		{
			
			if (m_OutputFormat == null)
			{
				throw new System.NullReferenceException("No output instance format defined");
			}
			return m_OutputQueue.size();
		}
		
		/// <summary> Gets an array containing the indices of all string attributes.
		/// 
		/// </summary>
		/// <param name="insts">the Instances to scan for string attributes. 
		/// </param>
		/// <returns> an array containing the indices of string attributes in
		/// the input structure. Will be zero-length if there are no
		/// string attributes
		/// </returns>
		protected internal virtual int[] getStringIndices(Instances insts)
		{
			
			// Scan through getting the indices of String attributes
			int[] index = new int[insts.numAttributes()];
			int indexSize = 0;
			for (int i = 0; i < insts.numAttributes(); i++)
			{
				if (insts.attribute(i).type() == Attribute.STRING)
				{
					index[indexSize++] = i;
				}
			}
			int[] result = new int[indexSize];
			Array.Copy(index, 0, result, 0, indexSize);
			return result;
		}
		
		/// <summary> Filters an entire set of instances through a filter and returns
		/// the new set. 
		/// 
		/// </summary>
		/// <param name="data">the data to be filtered
		/// </param>
		/// <param name="filter">the filter to be used
		/// </param>
		/// <returns> the filtered set of data
		/// </returns>
		/// <exception cref="Exception">if the filter can't be used successfully
		/// </exception>
		public static Instances useFilter(Instances data, Filter filter)
		{
			/*
			System.err.println(filter.getClass().getName() 
			+ " in:" + data.numInstances());
			*/
			for (int i = 0; i < data.numInstances(); i++)
			{
				filter.input(data.instance(i));
			}
			filter.batchFinished();
			Instances newData = filter.getOutputFormat();
			Instance processed;
			while ((processed = filter.output()) != null)
			{
				newData.add(processed);
			}
			
			/*
			System.err.println(filter.getClass().getName() 
			+ " out:" + newData.numInstances());
			*/
			return newData;
		}
		//Added by Alain Espinosa///////////////////////////////////////////////////////
		/// <summary> Filters an entire set of instances and returnsthe new set. 
		/// 
		/// </summary>
		/// <param name="data">the data to be filtered
		/// </param>
		/// <returns> the filtered set of data
		/// </returns>
		/// <exception cref="Exception">if the filter can't be used successfully
		/// </exception>
		public virtual Instances FilterInstances(Instances data)
		{
			setInputFormat(data);
			
			for (int i = 0; i < data.numInstances(); i++)
			{
				input(data.instance(i));
			}
			batchFinished();
			Instances newData = getOutputFormat();
			Instance processed;
			while ((processed = output()) != null)
			{
				newData.add(processed);
			}
			
			return newData;
		}
		//end of added by Alain Espinosa///////////////////////////////////////////////
		
		/// <summary> Method for testing filters.
		/// 
		/// </summary>
		/// <param name="argv">should contain the following arguments: <br>
		/// -i input_file <br>
		/// -o output_file <br>
		/// -c class_index <br>
		/// or -h for help on options
		/// </param>
		/// <exception cref="Exception">if something goes wrong or the user requests help on
		/// command options
		/// </exception>
        /// 
#if (!PocketPC)
		public static void  filterFile(Filter filter, System.String[] options)
		{
			
			bool debug = false;
			Instances data = null;
			//UPGRADE_ISSUE: Class hierarchy differences between 'java.io.Reader' and 'System.IO.StreamReader' may cause compilation errors. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1186'"
			System.IO.StreamReader input = null;
			System.IO.StreamWriter output = null;
			bool helpRequest;
			
			try
			{
				helpRequest = Utils.getFlag('h', options);
				
				if (Utils.getFlag('d', options))
				{
					debug = true;
				}
				System.String infileName = Utils.getOption('i', options);
				System.String outfileName = Utils.getOption('o', options);
				System.String classIndex = Utils.getOption('c', options);
				
				//			if (filter instanceof OptionHandler) 
				//			{
				//				((OptionHandler)filter).setOptions(options);
				//			}
				
				//			Utils.checkForRemainingOptions(options);
				if (helpRequest)
				{
					throw new System.Exception("Help requested.\n");
				}
				if (infileName.Length != 0)
				{
					//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.io.BufferedReader.BufferedReader'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
					//UPGRADE_WARNING: At least one expression was used more than once in the target code. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1181'"
					//UPGRADE_TODO: Constructor 'java.io.FileReader.FileReader' was converted to 'System.IO.StreamReader' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073'"
					input = new System.IO.StreamReader(new System.IO.StreamReader(infileName, System.Text.Encoding.Default).BaseStream, new System.IO.StreamReader(infileName, System.Text.Encoding.Default).CurrentEncoding);
				}
				else
				{
					//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.io.BufferedReader.BufferedReader'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
					//UPGRADE_WARNING: At least one expression was used more than once in the target code. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1181'"
					input = new System.IO.StreamReader(new System.IO.StreamReader(System.Console.OpenStandardInput(), System.Text.Encoding.Default).BaseStream, new System.IO.StreamReader(System.Console.OpenStandardInput(), System.Text.Encoding.Default).CurrentEncoding);
				}
				if (outfileName.Length != 0)
				{
					//UPGRADE_TODO: Constructor 'java.io.FileOutputStream.FileOutputStream' was converted to 'System.IO.FileStream.FileStream' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioFileOutputStreamFileOutputStream_javalangString'"
					output = new System.IO.StreamWriter(new System.IO.FileStream(outfileName, System.IO.FileMode.Create), System.Text.Encoding.Default);
				}
				else
				{
					output = new System.IO.StreamWriter(System.Console.OpenStandardOutput(), System.Text.Encoding.Default);
				}
				
				data = new Instances(input, 1);
				if (classIndex.Length != 0)
				{
					if (classIndex.Equals("first"))
					{
						data.ClassIndex = 0;
					}
					else if (classIndex.Equals("last"))
					{
						data.ClassIndex = data.numAttributes() - 1;
					}
					else
					{
						data.ClassIndex = System.Int32.Parse(classIndex) - 1;
					}
				}
			}
			catch (System.Exception ex)
			{
				System.String filterOptions = "";
				// Output the error and also the valid options
				//			if (filter instanceof OptionHandler) 
				//			{
				//				filterOptions += "\nFilter options:\n\n";
				////				Enumeration enu = ((OptionHandler)filter).listOptions();
				////				while (enu.hasMoreElements()) 
				////				{
				////					Option option = (Option) enu.nextElement();
				////					filterOptions += option.synopsis() + '\n'
				////						+ option.description() + "\n";
				////				}
				//			}
				
				System.String genericOptions = "\nGeneral options:\n\n" + "-h\n" + "\tGet help on available options.\n" + "\t(use -b -h for help on batch mode.)\n" + "-i <file>\n" + "\tThe name of the file containing input instances.\n" + "\tIf not supplied then instances will be read from stdin.\n" + "-o <file>\n" + "\tThe name of the file output instances will be written to.\n" + "\tIf not supplied then instances will be written to stdout.\n" + "-c <class index>\n" + "\tThe number of the attribute to use as the class.\n" + "\t\"first\" and \"last\" are also valid entries.\n" + "\tIf not supplied then no class is assigned.\n";
				
				//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Throwable.getMessage' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
				throw new System.Exception('\n' + ex.Message + filterOptions + genericOptions);
			}
			
			if (debug)
			{
				System.Console.Error.WriteLine("Setting input format");
			}
			bool printedHeader = false;
			if (filter.setInputFormat(data))
			{
				if (debug)
				{
					System.Console.Error.WriteLine("Getting output format");
				}
				//UPGRADE_TODO: Method 'java.io.PrintWriter.println' was converted to 'System.IO.TextWriter.WriteLine' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioPrintWriterprintln_javalangString'"
				output.WriteLine(filter.getOutputFormat().ToString());
				printedHeader = true;
			}
			
			// Pass all the instances to the filter
			while (data.readInstance(input))
			{
				if (debug)
				{
					System.Console.Error.WriteLine("Input instance to filter");
				}
				if (filter.input(data.instance(0)))
				{
					if (debug)
					{
						System.Console.Error.WriteLine("Filter said collect immediately");
					}
					if (!printedHeader)
					{
						throw new System.ApplicationException("Filter didn't return true from setInputFormat() " + "earlier!");
					}
					if (debug)
					{
						System.Console.Error.WriteLine("Getting output instance");
					}
					//UPGRADE_TODO: Method 'java.io.PrintWriter.println' was converted to 'System.IO.TextWriter.WriteLine' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioPrintWriterprintln_javalangString'"
					output.WriteLine(filter.output().ToString());
				}
				data.delete(0);
			}
			
			// Say that input has finished, and print any pending output instances
			if (debug)
			{
				System.Console.Error.WriteLine("Setting end of batch");
			}
			if (filter.batchFinished())
			{
				if (debug)
				{
					System.Console.Error.WriteLine("Filter said collect output");
				}
				if (!printedHeader)
				{
					if (debug)
					{
						System.Console.Error.WriteLine("Getting output format");
					}
					//UPGRADE_TODO: Method 'java.io.PrintWriter.println' was converted to 'System.IO.TextWriter.WriteLine' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioPrintWriterprintln_javalangString'"
					output.WriteLine(filter.getOutputFormat().ToString());
				}
				if (debug)
				{
					System.Console.Error.WriteLine("Getting output instance");
				}
				while (filter.numPendingOutput() > 0)
				{
					//UPGRADE_TODO: Method 'java.io.PrintWriter.println' was converted to 'System.IO.TextWriter.WriteLine' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioPrintWriterprintln_javalangString'"
					output.WriteLine(filter.output().ToString());
					if (debug)
					{
						System.Console.Error.WriteLine("Getting output instance");
					}
				}
			}
			if (debug)
			{
				System.Console.Error.WriteLine("Done");
			}
			
			if (output != null)
			{
				//UPGRADE_NOTE: Exceptions thrown by the equivalent in .NET of method 'java.io.PrintWriter.close' may be different. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1099'"
				output.Close();
			}
		}
	
		/// <summary> Method for testing filters ability to process multiple batches.
		/// 
		/// </summary>
		/// <param name="argv">should contain the following arguments:<br>
		/// -i (first) input file <br>
		/// -o (first) output file <br>
		/// -r (second) input file <br>
		/// -s (second) output file <br>
		/// -c class_index <br>
		/// or -h for help on options
		/// </param>
		/// <exception cref="Exception">if something goes wrong or the user requests help on
		/// command options
		/// </exception>
		public static void  batchFilterFile(Filter filter, System.String[] options)
		{
			
			Instances firstData = null;
			Instances secondData = null;
			//UPGRADE_ISSUE: Class hierarchy differences between 'java.io.Reader' and 'System.IO.StreamReader' may cause compilation errors. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1186'"
			System.IO.StreamReader firstInput = null;
			//UPGRADE_ISSUE: Class hierarchy differences between 'java.io.Reader' and 'System.IO.StreamReader' may cause compilation errors. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1186'"
			System.IO.StreamReader secondInput = null;
			System.IO.StreamWriter firstOutput = null;
			System.IO.StreamWriter secondOutput = null;
			bool helpRequest;
			try
			{
				helpRequest = Utils.getFlag('h', options);
				
				System.String fileName = Utils.getOption('i', options);
				if (fileName.Length != 0)
				{
					//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.io.BufferedReader.BufferedReader'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
					//UPGRADE_WARNING: At least one expression was used more than once in the target code. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1181'"
					//UPGRADE_TODO: Constructor 'java.io.FileReader.FileReader' was converted to 'System.IO.StreamReader' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073'"
					firstInput = new System.IO.StreamReader(new System.IO.StreamReader(fileName, System.Text.Encoding.Default).BaseStream, new System.IO.StreamReader(fileName, System.Text.Encoding.Default).CurrentEncoding);
				}
				else
				{
					throw new System.Exception("No first input file given.\n");
				}
				
				fileName = Utils.getOption('r', options);
				if (fileName.Length != 0)
				{
					//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.io.BufferedReader.BufferedReader'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
					//UPGRADE_WARNING: At least one expression was used more than once in the target code. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1181'"
					//UPGRADE_TODO: Constructor 'java.io.FileReader.FileReader' was converted to 'System.IO.StreamReader' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073'"
					secondInput = new System.IO.StreamReader(new System.IO.StreamReader(fileName, System.Text.Encoding.Default).BaseStream, new System.IO.StreamReader(fileName, System.Text.Encoding.Default).CurrentEncoding);
				}
				else
				{
					throw new System.Exception("No second input file given.\n");
				}
				
				fileName = Utils.getOption('o', options);
				if (fileName.Length != 0)
				{
					//UPGRADE_TODO: Constructor 'java.io.FileOutputStream.FileOutputStream' was converted to 'System.IO.FileStream.FileStream' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioFileOutputStreamFileOutputStream_javalangString'"
					firstOutput = new System.IO.StreamWriter(new System.IO.FileStream(fileName, System.IO.FileMode.Create), System.Text.Encoding.Default);
				}
				else
				{
					firstOutput = new System.IO.StreamWriter(System.Console.OpenStandardOutput(), System.Text.Encoding.Default);
				}
				
				fileName = Utils.getOption('s', options);
				if (fileName.Length != 0)
				{
					//UPGRADE_TODO: Constructor 'java.io.FileOutputStream.FileOutputStream' was converted to 'System.IO.FileStream.FileStream' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioFileOutputStreamFileOutputStream_javalangString'"
					secondOutput = new System.IO.StreamWriter(new System.IO.FileStream(fileName, System.IO.FileMode.Create), System.Text.Encoding.Default);
				}
				else
				{
					secondOutput = new System.IO.StreamWriter(System.Console.OpenStandardOutput(), System.Text.Encoding.Default);
				}
				System.String classIndex = Utils.getOption('c', options);
				
				//			if (filter instanceof OptionHandler) 
				//			{
				//				((OptionHandler)filter).setOptions(options);
				//			}
				Utils.checkForRemainingOptions(options);
				
				if (helpRequest)
				{
					throw new System.Exception("Help requested.\n");
				}
				firstData = new Instances(firstInput, 1);
				secondData = new Instances(secondInput, 1);
				if (!secondData.equalHeaders(firstData))
				{
					throw new System.Exception("Input file formats differ.\n");
				}
				if (classIndex.Length != 0)
				{
					if (classIndex.Equals("first"))
					{
						firstData.ClassIndex = 0;
						secondData.ClassIndex = 0;
					}
					else if (classIndex.Equals("last"))
					{
						firstData.ClassIndex = firstData.numAttributes() - 1;
						secondData.ClassIndex = secondData.numAttributes() - 1;
					}
					else
					{
						firstData.ClassIndex = System.Int32.Parse(classIndex) - 1;
						secondData.ClassIndex = System.Int32.Parse(classIndex) - 1;
					}
				}
			}
			catch (System.Exception ex)
			{
				System.String filterOptions = "";
				// Output the error and also the valid options
				//			if (filter instanceof OptionHandler) 
				//			{
				//				filterOptions += "\nFilter options:\n\n";
				//				Enumeration enu = ((OptionHandler)filter).listOptions();
				//				while (enu.hasMoreElements()) 
				//				{
				//					Option option = (Option) enu.nextElement();
				//					filterOptions += option.synopsis() + '\n'
				//						+ option.description() + "\n";
				//				}
				//			}
				
				System.String genericOptions = "\nGeneral options:\n\n" + "-h\n" + "\tGet help on available options.\n" + "-i <filename>\n" + "\tThe file containing first input instances.\n" + "-o <filename>\n" + "\tThe file first output instances will be written to.\n" + "-r <filename>\n" + "\tThe file containing second input instances.\n" + "-s <filename>\n" + "\tThe file second output instances will be written to.\n" + "-c <class index>\n" + "\tThe number of the attribute to use as the class.\n" + "\t\"first\" and \"last\" are also valid entries.\n" + "\tIf not supplied then no class is assigned.\n";
				
				//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Throwable.getMessage' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
				throw new System.Exception('\n' + ex.Message + filterOptions + genericOptions);
			}
			bool printedHeader = false;
			if (filter.setInputFormat(firstData))
			{
				//UPGRADE_TODO: Method 'java.io.PrintWriter.println' was converted to 'System.IO.TextWriter.WriteLine' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioPrintWriterprintln_javalangString'"
				firstOutput.WriteLine(filter.getOutputFormat().ToString());
				printedHeader = true;
			}
			
			// Pass all the instances to the filter
			while (firstData.readInstance(firstInput))
			{
				if (filter.input(firstData.instance(0)))
				{
					if (!printedHeader)
					{
						throw new System.ApplicationException("Filter didn't return true from setInputFormat() " + "earlier!");
					}
					//UPGRADE_TODO: Method 'java.io.PrintWriter.println' was converted to 'System.IO.TextWriter.WriteLine' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioPrintWriterprintln_javalangString'"
					firstOutput.WriteLine(filter.output().ToString());
				}
				firstData.delete(0);
			}
			
			// Say that input has finished, and print any pending output instances
			if (filter.batchFinished())
			{
				if (!printedHeader)
				{
					//UPGRADE_TODO: Method 'java.io.PrintWriter.println' was converted to 'System.IO.TextWriter.WriteLine' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioPrintWriterprintln_javalangString'"
					firstOutput.WriteLine(filter.getOutputFormat().ToString());
				}
				while (filter.numPendingOutput() > 0)
				{
					//UPGRADE_TODO: Method 'java.io.PrintWriter.println' was converted to 'System.IO.TextWriter.WriteLine' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioPrintWriterprintln_javalangString'"
					firstOutput.WriteLine(filter.output().ToString());
				}
			}
			
			if (firstOutput != null)
			{
				//UPGRADE_NOTE: Exceptions thrown by the equivalent in .NET of method 'java.io.PrintWriter.close' may be different. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1099'"
				firstOutput.Close();
			}
			printedHeader = false;
			if (filter.OutputFormatDefined)
			{
				//UPGRADE_TODO: Method 'java.io.PrintWriter.println' was converted to 'System.IO.TextWriter.WriteLine' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioPrintWriterprintln_javalangString'"
				secondOutput.WriteLine(filter.getOutputFormat().ToString());
				printedHeader = true;
			}
			// Pass all the second instances to the filter
			while (secondData.readInstance(secondInput))
			{
				if (filter.input(secondData.instance(0)))
				{
					if (!printedHeader)
					{
						throw new System.ApplicationException("Filter didn't return true from" + " isOutputFormatDefined() earlier!");
					}
					//UPGRADE_TODO: Method 'java.io.PrintWriter.println' was converted to 'System.IO.TextWriter.WriteLine' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioPrintWriterprintln_javalangString'"
					secondOutput.WriteLine(filter.output().ToString());
				}
				secondData.delete(0);
			}
			
			// Say that input has finished, and print any pending output instances
			if (filter.batchFinished())
			{
				if (!printedHeader)
				{
					//UPGRADE_TODO: Method 'java.io.PrintWriter.println' was converted to 'System.IO.TextWriter.WriteLine' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioPrintWriterprintln_javalangString'"
					secondOutput.WriteLine(filter.getOutputFormat().ToString());
				}
				while (filter.numPendingOutput() > 0)
				{
					//UPGRADE_TODO: Method 'java.io.PrintWriter.println' was converted to 'System.IO.TextWriter.WriteLine' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioPrintWriterprintln_javalangString'"
					secondOutput.WriteLine(filter.output().ToString());
				}
			}
			if (secondOutput != null)
			{
				//UPGRADE_NOTE: Exceptions thrown by the equivalent in .NET of method 'java.io.PrintWriter.close' may be different. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1099'"
				secondOutput.Close();
			}
		}
    #endif
    }
}