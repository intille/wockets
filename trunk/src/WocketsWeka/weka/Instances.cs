/*
*    Instances.java
*    Copyright (C) 1999 Eibe Frank
*
*/
using System;
using System.IO;
using WocketsWeka.Utils;


namespace weka.core
{
	
	/// <summary> Class for handling an ordered set of weighted instances. <p>
	/// 
	/// Typical usage (code from the main() method of this class): <p>
	/// 
	/// <code>
	/// ... <br>
	/// 
	/// // Read all the instances in the file <br>
	/// reader = new FileReader(filename); <br>
	/// instances = new Instances(reader); <br><br>
	/// 
	/// // Make the last attribute be the class <br>
	/// instances.setClassIndex(instances.numAttributes() - 1); <br><br>
	/// 
	/// // Print header and instances. <br>
	/// System.out.println("\nDataset:\n"); <br> 
	/// System.out.println(instances); <br><br>
	/// 
	/// ... <br>
	/// </code><p>
	/// 
	/// All methods that change a set of instances are safe, ie. a change
	/// of a set of instances does not affect any other sets of
	/// instances. All methods that change a datasets's attribute
	/// information clone the dataset before it is changed.
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <author>  Len Trigg (trigg@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.58.2.3 $ 
	/// </version>
#if !PocketPC
    [Serializable]
#endif
	public class Instances
	{
		/// <summary> Sets the class attribute.
		/// 
		/// </summary>
		/// <param name="att">attribute to be the class
		/// </param>
		virtual public Attribute Class
		{
			set
			{
				
				m_ClassIndex = value.index();
			}
			
		}
		/// <summary> Sets the class index of the set.
		/// If the class index is negative there is assumed to be no class.
		/// (ie. it is undefined)
		/// 
		/// </summary>
		/// <param name="classIndex">the new class index
		/// </param>
		/// <exception cref="IllegalArgumentException">if the class index is too big or < 0
		/// </exception>
		virtual public int ClassIndex
		{
			set
			{
				
				if (value >= numAttributes())
				{
					throw new System.ArgumentException("Invalid class index: " + value);
				}
				m_ClassIndex = value;
			}
			
		}
		/// <summary> Sets the relation's name.
		/// 
		/// </summary>
		/// <param name="newName">the new relation name.
		/// </param>
		virtual public System.String RelationName
		{
			set
			{
				
				m_RelationName = value;
			}
			
		}
		/// <summary>The filename extension that should be used for arff files </summary>
		public static System.String FILE_EXTENSION = ".arff";
		
		/// <summary>The filename extension that should be used for bin. serialized instances files </summary>
		public static System.String SERIALIZED_OBJ_FILE_EXTENSION = ".bsi";
		
		/// <summary>The keyword used to denote the start of an arff header </summary>
		internal static System.String ARFF_RELATION = "@relation";
		
		/// <summary>The keyword used to denote the start of the arff data section </summary>
		internal static System.String ARFF_DATA = "@data";
		
		/// <summary>The dataset's name. </summary>
		protected internal System.String m_RelationName;
		
		/// <summary>The attribute information. </summary>
		protected internal FastVector m_Attributes;
		/*  public invariant (\forall int i; 0 <= i && i < m_Attributes.size(); 
		m_Attributes.elementAt(i) != null);
		*/
		
		/// <summary>The instances. </summary>
		protected internal FastVector m_Instances;
		
		/// <summary>The class attribute's index </summary>
		protected internal int m_ClassIndex;
		//@ protected invariant classIndex() == m_ClassIndex;
		
		/// <summary>Buffer of values for sparse instance </summary>
		protected internal double[] m_ValueBuffer;
		
		/// <summary>Buffer of indices for sparse instance </summary>
		protected internal int[] m_IndicesBuffer;
		
		/// <summary> Reads an ARFF file from a reader, and assigns a weight of
		/// one to each instance. Lets the index of the class 
		/// attribute be undefined (negative).
		/// 
		/// </summary>
		/// <param name="reader">the reader
		/// </param>
		/// <exception cref="IOException">if the ARFF file is not read 
		/// successfully
		/// </exception>
		//UPGRADE_ISSUE: Class hierarchy differences between 'java.io.Reader' and 'System.IO.StreamReader' may cause compilation errors. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1186'"
		public Instances(System.IO.StreamReader reader)
		{
			
			StreamTokenizer tokenizer;
			
			tokenizer = new StreamTokenizer(reader);
			initTokenizer(tokenizer);
			readHeader(tokenizer);
			m_ClassIndex = - 1;
			m_Instances = new FastVector(1000);
			while (getInstance(tokenizer, true))
			{
			} ;
			compactify();
		}
		
		/// <summary> Reads the header of an ARFF file from a reader and 
		/// reserves space for the given number of instances. Lets
		/// the class index be undefined (negative).
		/// 
		/// </summary>
		/// <param name="reader">the reader
		/// </param>
		/// <param name="capacity">the capacity
		/// </param>
		/// <exception cref="IllegalArgumentException">if the header is not read successfully
		/// or the capacity is negative.
		/// </exception>
		/// <exception cref="IOException">if there is a problem with the reader.
		/// </exception>
		//@ requires capacity >= 0;
		//@ ensures classIndex() == -1;
		//UPGRADE_ISSUE: Class hierarchy differences between 'java.io.Reader' and 'System.IO.StreamReader' may cause compilation errors. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1186'"
		public Instances(System.IO.StreamReader reader, int capacity)
		{
			
			StreamTokenizer tokenizer;
			
			if (capacity < 0)
			{
				throw new System.ArgumentException("Capacity has to be positive!");
			}
			tokenizer = new StreamTokenizer(reader);
			initTokenizer(tokenizer);
			readHeader(tokenizer);
			m_ClassIndex = - 1;
			m_Instances = new FastVector(capacity);
		}
		
		/// <summary> Constructor copying all instances and references to
		/// the header information from the given set of instances.
		/// 
		/// </summary>
		/// <param name="instances">the set to be copied
		/// </param>
		public Instances(Instances dataset):this(dataset, dataset.numInstances())
		{
			
			dataset.copyInstances(0, this, dataset.numInstances());
		}
		
		/// <summary> Constructor creating an empty set of instances. Copies references
		/// to the header information from the given set of instances. Sets
		/// the capacity of the set of instances to 0 if its negative.
		/// 
		/// </summary>
		/// <param name="instances">the instances from which the header 
		/// information is to be taken
		/// </param>
		/// <param name="capacity">the capacity of the new dataset 
		/// </param>
		public Instances(Instances dataset, int capacity)
		{
			
			if (capacity < 0)
			{
				capacity = 0;
			}
			
			// Strings only have to be "shallow" copied because
			// they can't be modified.
			m_ClassIndex = dataset.m_ClassIndex;
			m_RelationName = dataset.m_RelationName;
			m_Attributes = dataset.m_Attributes;
			m_Instances = new FastVector(capacity);
		}
		
		/// <summary> Creates a new set of instances by copying a 
		/// subset of another set.
		/// 
		/// </summary>
		/// <param name="source">the set of instances from which a subset 
		/// is to be created
		/// </param>
		/// <param name="first">the index of the first instance to be copied
		/// </param>
		/// <param name="toCopy">the number of instances to be copied
		/// </param>
		/// <exception cref="IllegalArgumentException">if first and toCopy are out of range
		/// </exception>
		//@ requires 0 <= first;
		//@ requires 0 <= toCopy;
		//@ requires first + toCopy <= source.numInstances();
		public Instances(Instances source, int first, int toCopy):this(source, toCopy)
		{
			
			if ((first < 0) || ((first + toCopy) > source.numInstances()))
			{
				throw new System.ArgumentException("Parameters first and/or toCopy out " + "of range");
			}
			source.copyInstances(first, this, toCopy);
		}
		
		/// <summary> Creates an empty set of instances. Uses the given
		/// attribute information. Sets the capacity of the set of 
		/// instances to 0 if its negative. Given attribute information
		/// must not be changed after this constructor has been used.
		/// 
		/// </summary>
		/// <param name="name">the name of the relation
		/// </param>
		/// <param name="attInfo">the attribute information
		/// </param>
		/// <param name="capacity">the capacity of the set
		/// </param>
		public Instances(System.String name, FastVector attInfo, int capacity)
		{
			
			m_RelationName = name;
			m_ClassIndex = - 1;
			m_Attributes = attInfo;
			for (int i = 0; i < numAttributes(); i++)
			{
				attribute(i).Index = i;
			}
			m_Instances = new FastVector(capacity);
		}
		
		/// <summary> Create a copy of the structure, but "cleanse" string types (i.e.
		/// doesn't contain references to the strings seen in the past).
		/// 
		/// </summary>
		/// <returns> a copy of the instance structure.
		/// </returns>
		public virtual Instances stringFreeStructure()
		{
			
			FastVector atts = (FastVector) m_Attributes.copy();
			for (int i = 0; i < atts.size(); i++)
			{
				Attribute att = (Attribute) atts.elementAt(i);
				if (att.type() == Attribute.STRING)
				{
					atts.setXmlElementAt(new Attribute(att.name(), (FastVector) null), i);
				}
			}
			Instances result = new Instances(relationName(), atts, 0);
			result.m_ClassIndex = m_ClassIndex;
			return result;
		}
		
		/// <summary> Adds one instance to the end of the set. 
		/// Shallow copies instance before it is added. Increases the
		/// size of the dataset if it is not large enough. Does not
		/// check if the instance is compatible with the dataset.
		/// 
		/// </summary>
		/// <param name="instance">the instance to be added
		/// </param>
		public virtual void  add(Instance instance)
		{
			Instance newInstance = (Instance) instance.copy();
			
			newInstance.Dataset = this;
			m_Instances.addElement(newInstance);
		}
		
		/// <summary> Returns an attribute.
		/// 
		/// </summary>
		/// <param name="index">the attribute's index
		/// </param>
		/// <returns> the attribute at the given position
		/// </returns>
		//@ requires 0 <= index;
		//@ requires index < m_Attributes.size();
		//@ ensures \result != null;
		public virtual Attribute attribute(int index)
		{
			
			return (Attribute) m_Attributes.elementAt(index);
		}
		
		/// <summary> Returns an attribute given its name. If there is more than
		/// one attribute with the same name, it returns the first one.
		/// Returns null if the attribute can't be found.
		/// 
		/// </summary>
		/// <param name="name">the attribute's name
		/// </param>
		/// <returns> the attribute with the given name, null if the
		/// attribute can't be found
		/// </returns>
		public virtual Attribute attribute(System.String name)
		{
			
			for (int i = 0; i < numAttributes(); i++)
			{
				if (attribute(i).name().Equals(name))
				{
					return attribute(i);
				}
			}
			return null;
		}
		
		/// <summary> Checks for string attributes in the dataset
		/// 
		/// </summary>
		/// <returns> true if string attributes are present, false otherwise
		/// </returns>
		public virtual bool checkForStringAttributes()
		{
			
			int i = 0;
			
			while (i < m_Attributes.size())
			{
				if (attribute(i++).String)
				{
					return true;
				}
			}
			return false;
		}
		
		/// <summary> Checks if the given instance is compatible
		/// with this dataset. Only looks at the size of
		/// the instance and the ranges of the values for 
		/// nominal and string attributes.
		/// 
		/// </summary>
		/// <returns> true if the instance is compatible with the dataset 
		/// </returns>
		public virtual bool checkInstance(Instance instance)
		{
			
			if (instance.numAttributes() != numAttributes())
			{
				return false;
			}
			for (int i = 0; i < numAttributes(); i++)
			{
				if (instance.isMissing(i))
				{
					continue;
				}
				else if (attribute(i).Nominal || attribute(i).String)
				{
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					if (!(Utils.eq(instance.value_Renamed(i), (double) instance.value_Renamed(i))))
					{
						return false;
					}
					else if (Utils.sm(instance.value_Renamed(i), 0) || Utils.gr(instance.value_Renamed(i), attribute(i).numValues()))
					{
						return false;
					}
				}
			}
			return true;
		}
		
		/// <summary> Returns the class attribute.
		/// 
		/// </summary>
		/// <returns> the class attribute
		/// </returns>
		/// <exception cref="Exception">if the class is not set
		/// </exception>
		//@ requires classIndex() >= 0;
		public virtual Attribute classAttribute()
		{
			
			if (m_ClassIndex < 0)
			{
				throw new Exception("Class index is negative (not set)!");
			}
			return attribute(m_ClassIndex);
		}
		
		/// <summary> Returns the class attribute's index. Returns negative number
		/// if it's undefined.
		/// 
		/// </summary>
		/// <returns> the class index as an integer
		/// </returns>
		// ensures \result == m_ClassIndex;
		public virtual int classIndex()
		{
			
			return m_ClassIndex;
		}
		
		/// <summary> Compactifies the set of instances. Decreases the capacity of
		/// the set so that it matches the number of instances in the set.
		/// </summary>
		public virtual void  compactify()
		{
			
			m_Instances.trimToSize();
		}
		
		/// <summary> Removes all instances from the set.</summary>
		public virtual void  delete()
		{
			
			m_Instances = new FastVector();
		}
		
		/// <summary> Removes an instance at the given position from the set.
		/// 
		/// </summary>
		/// <param name="index">the instance's position
		/// </param>
		//@ requires 0 <= index && index < numInstances();
		public virtual void  delete(int index)
		{
			
			m_Instances.removeElementAt(index);
		}
		
		/// <summary> Deletes an attribute at the given position 
		/// (0 to numAttributes() - 1). A deep copy of the attribute
		/// information is performed before the attribute is deleted.
		/// 
		/// </summary>
		/// <param name="pos">the attribute's position
		/// </param>
		/// <exception cref="IllegalArgumentException">if the given index is out of range 
		/// or the class attribute is being deleted
		/// </exception>
		//@ requires 0 <= position && position < numAttributes();
		//@ requires position != classIndex();
		public virtual void  deleteAttributeAt(int position)
		{
			
			if ((position < 0) || (position >= m_Attributes.size()))
			{
				throw new System.ArgumentException("Index out of range");
			}
			if (position == m_ClassIndex)
			{
				throw new System.ArgumentException("Can't delete class attribute");
			}
			freshAttributeInfo();
			if (m_ClassIndex > position)
			{
				m_ClassIndex--;
			}
			m_Attributes.removeElementAt(position);
			for (int i = position; i < m_Attributes.size(); i++)
			{
				Attribute current = (Attribute) m_Attributes.elementAt(i);
				current.Index = current.index() - 1;
			}
			for (int i = 0; i < numInstances(); i++)
			{
				instance(i).forceDeleteAttributeAt(position);
			}
		}
		
		/// <summary> Deletes all string attributes in the dataset. A deep copy of the attribute
		/// information is performed before an attribute is deleted.
		/// 
		/// </summary>
		/// <exception cref="IllegalArgumentException">if string attribute couldn't be 
		/// successfully deleted (probably because it is the class attribute).
		/// </exception>
		public virtual void  deleteStringAttributes()
		{
			
			int i = 0;
			while (i < m_Attributes.size())
			{
				if (attribute(i).String)
				{
					deleteAttributeAt(i);
				}
				else
				{
					i++;
				}
			}
		}
		
		/// <summary> Removes all instances with missing values for a particular
		/// attribute from the dataset.
		/// 
		/// </summary>
		/// <param name="attIndex">the attribute's index
		/// </param>
		//@ requires 0 <= attIndex && attIndex < numAttributes();
		public virtual void  deleteWithMissing(int attIndex)
		{
			
			FastVector newInstances = new FastVector(numInstances());
			
			for (int i = 0; i < numInstances(); i++)
			{
				if (!instance(i).isMissing(attIndex))
				{
					newInstances.addElement(instance(i));
				}
			}
			m_Instances = newInstances;
		}
		
		/// <summary> Removes all instances with missing values for a particular
		/// attribute from the dataset.
		/// 
		/// </summary>
		/// <param name="att">the attribute
		/// </param>
		public virtual void  deleteWithMissing(Attribute att)
		{
			
			deleteWithMissing(att.index());
		}
		
		/// <summary> Removes all instances with a missing class value
		/// from the dataset.
		/// 
		/// </summary>
		/// <exception cref="Exception">if class is not set
		/// </exception>
		public virtual void  deleteWithMissingClass()
		{
			
			if (m_ClassIndex < 0)
			{
				throw new Exception("Class index is negative (not set)!");
			}
			deleteWithMissing(m_ClassIndex);
		}
		
		/// <summary> Returns an enumeration of all the attributes.
		/// 
		/// </summary>
		/// <returns> enumeration of all the attributes.
		/// </returns>
		public virtual System.Collections.IEnumerator enumerateAttributes()
		{
			
			return m_Attributes.elements(m_ClassIndex);
		}
		
		/// <summary> Returns an enumeration of all instances in the dataset.
		/// 
		/// </summary>
		/// <returns> enumeration of all instances in the dataset
		/// </returns>
		public virtual System.Collections.IEnumerator enumerateInstances()
		{
			
			return m_Instances.elements();
		}
		
		/// <summary> Checks if two headers are equivalent.
		/// 
		/// </summary>
		/// <param name="dataset">another dataset
		/// </param>
		/// <returns> true if the header of the given dataset is equivalent 
		/// to this header
		/// </returns>
		public virtual bool equalHeaders(Instances dataset)
		{
			
			// Check class and all attributes
			if (m_ClassIndex != dataset.m_ClassIndex)
			{
				return false;
			}
			if (m_Attributes.size() != dataset.m_Attributes.size())
			{
				return false;
			}
			for (int i = 0; i < m_Attributes.size(); i++)
			{
				if (!(attribute(i).Equals(dataset.attribute(i))))
				{
					return false;
				}
			}
			return true;
		}
		
		/// <summary> Returns the first instance in the set.
		/// 
		/// </summary>
		/// <returns> the first instance in the set
		/// </returns>
		//@ requires numInstances() > 0;
		public virtual Instance firstInstance()
		{
			
			return (Instance) m_Instances.firstXmlElement();
		}
		
		/// <summary> Returns a random number generator. The initial seed of the random
		/// number generator depends on the given seed and the hash code of
		/// a string representation of a instances chosen based on the given
		/// seed. 
		/// 
		/// </summary>
		/// <param name="seed">the given seed
		/// </param>
		/// <returns> the random number generator
		/// </returns>
		public virtual System.Random getRandomNumberGenerator(long seed)
		{
			
			//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.util.Random.Random'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
			System.Random r = new System.Random((System.Int32) seed);
			//UPGRADE_TODO: The differences in the expected value  of parameters for method 'java.util.Random.setSeed'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
			r = new System.Random((System.Int32) (instance(r.Next(numInstances())).ToString().GetHashCode() + seed));
			return r;
		}
		
		/// <summary> Inserts an attribute at the given position (0 to 
		/// numAttributes()) and sets all values to be missing.
		/// Shallow copies the attribute before it is inserted, and performs
		/// a deep copy of the existing attribute information.
		/// 
		/// </summary>
		/// <param name="att">the attribute to be inserted
		/// </param>
		/// <param name="pos">the attribute's position
		/// </param>
		/// <exception cref="IllegalArgumentException">if the given index is out of range
		/// </exception>
		//@ requires 0 <= position;
		//@ requires position <= numAttributes();
		public virtual void  insertAttributeAt(Attribute att, int position)
		{
			
			if ((position < 0) || (position > m_Attributes.size()))
			{
				throw new System.ArgumentException("Index out of range");
			}
			att = (Attribute) att.copy();
			freshAttributeInfo();
			att.Index = position;
			m_Attributes.insertElementAt(att, position);
			for (int i = position + 1; i < m_Attributes.size(); i++)
			{
				Attribute current = (Attribute) m_Attributes.elementAt(i);
				current.Index = current.index() + 1;
			}
			for (int i = 0; i < numInstances(); i++)
			{
				instance(i).forceInsertAttributeAt(position);
			}
			if (m_ClassIndex >= position)
			{
				m_ClassIndex++;
			}
		}
		
		/// <summary> Returns the instance at the given position.
		/// 
		/// </summary>
		/// <param name="index">the instance's index
		/// </param>
		/// <returns> the instance at the given position
		/// </returns>
		//@ requires 0 <= index;
		//@ requires index < numInstances();
		public virtual Instance instance(int index)
		{
			return (Instance) m_Instances.elementAt(index);
		}
		
		/// <summary> Returns the kth-smallest attribute value of a numeric attribute.
		/// Note that calling this method will change the order of the data!
		/// 
		/// </summary>
		/// <param name="att">the Attribute object
		/// </param>
		/// <param name="k">the value of k
		/// </param>
		/// <returns> the kth-smallest value
		/// </returns>
		public virtual double kthSmallestValue(Attribute att, int k)
		{
			
			return kthSmallestValue(att.index(), k);
		}
		
		/// <summary> Returns the kth-smallest attribute value of a numeric attribute.
		/// Note that calling this method will change the order of the data!
		/// The number of non-missing values in the data must be as least
		/// as last as k for this to work.
		/// 
		/// </summary>
		/// <param name="attIndex">the attribute's index
		/// </param>
		/// <param name="k">the value of k
		/// </param>
		/// <returns> the kth-smallest value
		/// </returns>
		public virtual double kthSmallestValue(int attIndex, int k)
		{
			
			if (!attribute(attIndex).Numeric)
			{
				throw new System.ArgumentException("Instances: attribute must be numeric to compute kth-smallest value.");
			}
			
			int i, j;
			
			// move all instances with missing values to end
			j = numInstances() - 1;
			i = 0;
			while (i <= j)
			{
				if (instance(j).isMissing(attIndex))
				{
					j--;
				}
				else
				{
					if (instance(i).isMissing(attIndex))
					{
						swap(i, j);
						j--;
					}
					i++;
				}
			}
			
			if ((k < 0) || (k > j))
			{
				throw new System.ArgumentException("Instances: value for k for computing kth-smallest value too large.");
			}
			
			return instance(select(attIndex, 0, j, k)).value_Renamed(attIndex);
		}
		
		/// <summary> Returns the last instance in the set.
		/// 
		/// </summary>
		/// <returns> the last instance in the set
		/// </returns>
		//@ requires numInstances() > 0;
		public virtual Instance lastInstance()
		{
			
			return (Instance) m_Instances.lastElement();
		}
		
		/// <summary> Returns the mean (mode) for a numeric (nominal) attribute as
		/// a floating-point value. Returns 0 if the attribute is neither nominal nor 
		/// numeric. If all values are missing it returns zero.
		/// 
		/// </summary>
		/// <param name="attIndex">the attribute's index
		/// </param>
		/// <returns> the mean or the mode
		/// </returns>
		public virtual double meanOrMode(int attIndex)
		{
			
			double result, found;
			int[] counts;
			
			if (attribute(attIndex).Numeric)
			{
				result = found = 0;
				for (int j = 0; j < numInstances(); j++)
				{
					if (!instance(j).isMissing(attIndex))
					{
						found += instance(j).weight();
						result += instance(j).weight() * instance(j).value_Renamed(attIndex);
					}
				}
				if (found <= 0)
				{
					return 0;
				}
				else
				{
					return result / found;
				}
			}
			else if (attribute(attIndex).Nominal)
			{
				counts = new int[attribute(attIndex).numValues()];
				for (int j = 0; j < numInstances(); j++)
				{
					if (!instance(j).isMissing(attIndex))
					{
						//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
						counts[(int) instance(j).value_Renamed(attIndex)] = (int) (counts[(int) instance(j).value_Renamed(attIndex)] + instance(j).weight());
					}
				}
				return (double) Utils.maxIndex(counts);
			}
			else
			{
				return 0;
			}
		}
		
		/// <summary> Returns the mean (mode) for a numeric (nominal) attribute as a
		/// floating-point value.  Returns 0 if the attribute is neither
		/// nominal nor numeric.  If all values are missing it returns zero.
		/// 
		/// </summary>
		/// <param name="att">the attribute
		/// </param>
		/// <returns> the mean or the mode 
		/// </returns>
		public virtual double meanOrMode(Attribute att)
		{
			
			return meanOrMode(att.index());
		}
		
		/// <summary> Returns the number of attributes.
		/// 
		/// </summary>
		/// <returns> the number of attributes as an integer
		/// </returns>
		//@ ensures \result == m_Attributes.size();
		public virtual int numAttributes()
		{
			
			return m_Attributes.size();
		}
		
		/// <summary> Returns the number of class labels.
		/// 
		/// </summary>
		/// <returns> the number of class labels as an integer if the class 
		/// attribute is nominal, 1 otherwise.
		/// </returns>
		/// <exception cref="Exception">if the class is not set
		/// </exception>
		//@ requires classIndex() >= 0;
		public virtual int numClasses()
		{
			
			if (m_ClassIndex < 0)
			{
				throw new Exception("Class index is negative (not set)!");
			}
			if (!classAttribute().Nominal)
			{
				return 1;
			}
			else
			{
				return classAttribute().numValues();
			}
		}
		
		/// <summary> Returns the number of distinct values of a given attribute.
		/// Returns the number of instances if the attribute is a
		/// string attribute. The value 'missing' is not counted.
		/// 
		/// </summary>
		/// <param name="attIndex">the attribute
		/// </param>
		/// <returns> the number of distinct values of a given attribute
		/// </returns>
		//@ requires 0 <= attIndex;
		//@ requires attIndex < numAttributes();
		public virtual int numDistinctValues(int attIndex)
		{
			
			if (attribute(attIndex).Numeric)
			{
				double[] attVals = attributeToDoubleArray(attIndex);
				int[] sorted = Utils.sort(attVals);
				double prev = 0;
				int counter = 0;
				for (int i = 0; i < sorted.Length; i++)
				{
					Instance current = instance(sorted[i]);
					if (current.isMissing(attIndex))
					{
						break;
					}
					if ((i == 0) || (current.value_Renamed(attIndex) > prev))
					{
						prev = current.value_Renamed(attIndex);
						counter++;
					}
				}
				return counter;
			}
			else
			{
				return attribute(attIndex).numValues();
			}
		}
		
		/// <summary> Returns the number of distinct values of a given attribute.
		/// Returns the number of instances if the attribute is a
		/// string attribute. The value 'missing' is not counted.
		/// 
		/// </summary>
		/// <param name="att">the attribute
		/// </param>
		/// <returns> the number of distinct values of a given attribute
		/// </returns>
		public virtual int numDistinctValues(Attribute att)
		{
			
			return numDistinctValues(att.index());
		}
		
		/// <summary> Returns the number of instances in the dataset.
		/// 
		/// </summary>
		/// <returns> the number of instances in the dataset as an integer
		/// </returns>
		//@ ensures \result == m_Instances.size();
		public virtual int numInstances()
		{
			
			return m_Instances.size();
		}
		
		/// <summary> Shuffles the instances in the set so that they are ordered 
		/// randomly.
		/// 
		/// </summary>
		/// <param name="random">a random number generator
		/// </param>
		public virtual void  randomize(System.Random random)
		{
			
			for (int j = numInstances() - 1; j > 0; j--)
				swap(j, random.Next(j + 1));
		}
		
		/// <summary> Reads a single instance from the reader and appends it
		/// to the dataset.  Automatically expands the dataset if it
		/// is not large enough to hold the instance. This method does
		/// not check for carriage return at the end of the line.
		/// 
		/// </summary>
		/// <param name="reader">the reader 
		/// </param>
		/// <returns> false if end of file has been reached
		/// </returns>
		/// <exception cref="IOException">if the information is not read 
		/// successfully
		/// </exception>
		//UPGRADE_ISSUE: Class hierarchy differences between 'java.io.Reader' and 'System.IO.StreamReader' may cause compilation errors. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1186'"
		public virtual bool readInstance(System.IO.StreamReader reader)
		{
			StreamTokenizer tokenizer = new StreamTokenizer(reader);
			
			initTokenizer(tokenizer);
			return getInstance(tokenizer, false);
		}
		
		/// <summary> Returns the relation's name.
		/// 
		/// </summary>
		/// <returns> the relation's name as a string
		/// </returns>
		//@ ensures \result == m_RelationName;
		public virtual System.String relationName()
		{
			
			return m_RelationName;
		}
		
		/// <summary> Renames an attribute. This change only affects this
		/// dataset.
		/// 
		/// </summary>
		/// <param name="att">the attribute's index
		/// </param>
		/// <param name="name">the new name
		/// </param>
		public virtual void  renameAttribute(int att, System.String name)
		{
			
			Attribute newAtt = attribute(att).copy(name);
			FastVector newVec = new FastVector(numAttributes());
			
			for (int i = 0; i < numAttributes(); i++)
			{
				if (i == att)
				{
					newVec.addElement(newAtt);
				}
				else
				{
					newVec.addElement(attribute(i));
				}
			}
			m_Attributes = newVec;
		}
		
		/// <summary> Renames an attribute. This change only affects this
		/// dataset.
		/// 
		/// </summary>
		/// <param name="att">the attribute
		/// </param>
		/// <param name="name">the new name
		/// </param>
		public virtual void  renameAttribute(Attribute att, System.String name)
		{
			
			renameAttribute(att.index(), name);
		}
		
		/// <summary> Renames the value of a nominal (or string) attribute value. This
		/// change only affects this dataset.
		/// 
		/// </summary>
		/// <param name="att">the attribute's index
		/// </param>
		/// <param name="val">the value's index
		/// </param>
		/// <param name="name">the new name 
		/// </param>
		public virtual void  renameAttributeValue(int att, int val, System.String name)
		{
			
			Attribute newAtt = (Attribute) attribute(att).copy();
			FastVector newVec = new FastVector(numAttributes());
			
			newAtt.setValue(val, name);
			for (int i = 0; i < numAttributes(); i++)
			{
				if (i == att)
				{
					newVec.addElement(newAtt);
				}
				else
				{
					newVec.addElement(attribute(i));
				}
			}
			m_Attributes = newVec;
		}
		
		/// <summary> Renames the value of a nominal (or string) attribute value. This
		/// change only affects this dataset.
		/// 
		/// </summary>
		/// <param name="att">the attribute
		/// </param>
		/// <param name="val">the value
		/// </param>
		/// <param name="name">the new name
		/// </param>
		public virtual void  renameAttributeValue(Attribute att, System.String val, System.String name)
		{
			
			int v = att.indexOfValue(val);
			if (v == - 1)
				throw new System.ArgumentException(val + " not found");
			renameAttributeValue(att.index(), v, name);
		}
		
		/// <summary> Creates a new dataset of the same size using random sampling
		/// with replacement.
		/// 
		/// </summary>
		/// <param name="random">a random number generator
		/// </param>
		/// <returns> the new dataset
		/// </returns>
		public virtual Instances resample(System.Random random)
		{
			
			Instances newData = new Instances(this, numInstances());
			while (newData.numInstances() < numInstances())
			{
				newData.add(instance(random.Next(numInstances())));
			}
			return newData;
		}
		
		/// <summary> Creates a new dataset of the same size using random sampling
		/// with replacement according to the current instance weights. The
		/// weights of the instances in the new dataset are set to one.
		/// 
		/// </summary>
		/// <param name="random">a random number generator
		/// </param>
		/// <returns> the new dataset
		/// </returns>
		public virtual Instances resampleWithWeights(System.Random random)
		{
			
			double[] weights = new double[numInstances()];
			for (int i = 0; i < weights.Length; i++)
			{
				weights[i] = instance(i).weight();
			}
			return resampleWithWeights(random, weights);
		}
		
		
		/// <summary> Creates a new dataset of the same size using random sampling
		/// with replacement according to the given weight vector. The
		/// weights of the instances in the new dataset are set to one.
		/// The length of the weight vector has to be the same as the
		/// number of instances in the dataset, and all weights have to
		/// be positive.
		/// 
		/// </summary>
		/// <param name="random">a random number generator
		/// </param>
		/// <param name="weights">the weight vector
		/// </param>
		/// <returns> the new dataset
		/// </returns>
		/// <exception cref="IllegalArgumentException">if the weights array is of the wrong
		/// length or contains negative weights.
		/// </exception>
		public virtual Instances resampleWithWeights(System.Random random, double[] weights)
		{
			
			if (weights.Length != numInstances())
			{
				throw new System.ArgumentException("weights.length != numInstances.");
			}
			Instances newData = new Instances(this, numInstances());
			if (numInstances() == 0)
			{
				return newData;
			}
			double[] probabilities = new double[numInstances()];
			double sumProbs = 0, sumOfWeights = Utils.sum(weights);
			for (int i = 0; i < numInstances(); i++)
			{
				sumProbs += random.NextDouble();
				probabilities[i] = sumProbs;
			}
			Utils.normalize(probabilities, sumProbs / sumOfWeights);
			
			// Make sure that rounding errors don't mess things up
			probabilities[numInstances() - 1] = sumOfWeights;
			int k = 0; int l = 0;
			sumProbs = 0;
			while ((k < numInstances() && (l < numInstances())))
			{
				if (weights[l] < 0)
				{
					throw new System.ArgumentException("Weights have to be positive.");
				}
				sumProbs += weights[l];
				while ((k < numInstances()) && (probabilities[k] <= sumProbs))
				{
					newData.add(instance(l));
					newData.instance(k).Weight = 1;
					k++;
				}
				l++;
			}
			return newData;
		}
		
		/// <summary> Sorts the instances based on an attribute. For numeric attributes, 
		/// instances are sorted in ascending order. For nominal attributes, 
		/// instances are sorted based on the attribute label ordering 
		/// specified in the header. Instances with missing values for the 
		/// attribute are placed at the end of the dataset.
		/// 
		/// </summary>
		/// <param name="attIndex">the attribute's index
		/// </param>
		public virtual void  sort(int attIndex)
		{
			
			int i, j;
			
			// move all instances with missing values to end
			j = numInstances() - 1;
			i = 0;
			while (i <= j)
			{
				if (instance(j).isMissing(attIndex))
				{
					j--;
				}
				else
				{
					if (instance(i).isMissing(attIndex))
					{
						swap(i, j);
						j--;
					}
					i++;
				}
			}
			quickSort(attIndex, 0, j);
		}
		
		/// <summary> Sorts the instances based on an attribute. For numeric attributes, 
		/// instances are sorted into ascending order. For nominal attributes, 
		/// instances are sorted based on the attribute label ordering 
		/// specified in the header. Instances with missing values for the 
		/// attribute are placed at the end of the dataset.
		/// 
		/// </summary>
		/// <param name="att">the attribute
		/// </param>
		public virtual void  sort(Attribute att)
		{
			
			sort(att.index());
		}
		
		/// <summary> Stratifies a set of instances according to its class values 
		/// if the class attribute is nominal (so that afterwards a 
		/// stratified cross-validation can be performed).
		/// 
		/// </summary>
		/// <param name="numFolds">the number of folds in the cross-validation
		/// </param>
		/// <exception cref="Exception">if the class is not set
		/// </exception>
		public virtual void  stratify(int numFolds)
		{
			
			if (numFolds <= 0)
			{
				throw new System.ArgumentException("Number of folds must be greater than 1");
			}
			if (m_ClassIndex < 0)
			{
				throw new Exception("Class index is negative (not set)!");
			}
			if (classAttribute().Nominal)
			{
				
				// sort by class
				int index = 1;
				while (index < numInstances())
				{
					Instance instance1 = instance(index - 1);
					for (int j = index; j < numInstances(); j++)
					{
						Instance instance2 = instance(j);
						if ((instance1.classValue() == instance2.classValue()) || (instance1.classIsMissing() && instance2.classIsMissing()))
						{
							swap(index, j);
							index++;
						}
					}
					index++;
				}
				stratStep(numFolds);
			}
		}
		
		/// <summary> Computes the sum of all the instances' weights.
		/// 
		/// </summary>
		/// <returns> the sum of all the instances' weights as a double
		/// </returns>
		public virtual double sumOfWeights()
		{
			
			double sum = 0;
			
			for (int i = 0; i < numInstances(); i++)
			{
				sum += instance(i).weight();
			}
			return sum;
		}
		
		/// <summary> Creates the test set for one fold of a cross-validation on 
		/// the dataset.
		/// 
		/// </summary>
		/// <param name="numFolds">the number of folds in the cross-validation. Must
		/// be greater than 1.
		/// </param>
		/// <param name="numFold">0 for the first fold, 1 for the second, ...
		/// </param>
		/// <returns> the test set as a set of weighted instances
		/// </returns>
		/// <exception cref="IllegalArgumentException">if the number of folds is less than 2
		/// or greater than the number of instances.
		/// </exception>
		//@ requires 2 <= numFolds && numFolds < numInstances();
		//@ requires 0 <= numFold && numFold < numFolds;
		public virtual Instances testCV(int numFolds, int numFold)
		{
			
			int numInstForFold, first, offset;
			Instances test;
			
			if (numFolds < 2)
			{
				throw new System.ArgumentException("Number of folds must be at least 2!");
			}
			if (numFolds > numInstances())
			{
				throw new System.ArgumentException("Can't have more folds than instances!");
			}
			numInstForFold = numInstances() / numFolds;
			if (numFold < numInstances() % numFolds)
			{
				numInstForFold++;
				offset = numFold;
			}
			else
				offset = numInstances() % numFolds;
			test = new Instances(this, numInstForFold);
			first = numFold * (numInstances() / numFolds) + offset;
			copyInstances(first, test, numInstForFold);
			return test;
		}


        /// <summary> Returns the dataset as a string in ARFF format. Strings
        /// are quoted if they contain whitespace characters, or if they
        /// are a question mark.
        /// 
        /// </summary>
        /// <returns> the dataset in ARFF format as a string
        /// </returns>
        public System.String ToCSVString()
        {

            System.Text.StringBuilder text = new System.Text.StringBuilder();

           // text.Append(ARFF_RELATION).Append(" ").Append(Utils.quote(m_RelationName)).Append("\n\n");
            for (int i = 0; i < numAttributes(); i++)
            {
                text.Append(attribute(i).name()).Append(",");
            }

            text.Append("\n");
            for (int i = 0; i < numInstances(); i++)
            {
                text.Append(instance(i));
                if (i < numInstances() - 1)
                {
                    text.Append('\n');
                }
            }
            return text.ToString();
        }



        public void ToArff(string filename)
        {
            TextWriter tw = new StreamWriter(filename);

            //System.Text.StringBuilder text = new System.Text.StringBuilder();

            tw.Write(ARFF_RELATION+" "+Utils.quote(m_RelationName)+"\n\n");
            for (int i = 0; i < numAttributes(); i++)
            {
                tw.Write(attribute(i)+"\n");
            }
            tw.Write("\n"+ARFF_DATA+"\n");
            for (int i = 0; i < numInstances(); i++)
            {
                tw.Write(instance(i));
                if (i < numInstances() - 1)
                {
                    tw.Write('\n');
                }
            }
            tw.Write('\n');
            tw.Close();
        }



        public void ToCSV(string filename)
        {

            //System.Text.StringBuilder text = new System.Text.StringBuilder();
            TextWriter tw = new StreamWriter(filename);


            for (int i = 0; i < numAttributes(); i++)
            {
                tw.Write(attribute(i).name());
                if (i<numAttributes()-1)
                    tw.Write(',');
            }

            tw.Write("\n");
            for (int i = 0; i < numInstances(); i++)
            {
                tw.Write(instance(i));
                if (i < numInstances() - 1)
                {
                    tw.Write('\n');
                }
            }
            tw.Write('\n');
            tw.Close();
        }

		/// <summary> Returns the dataset as a string in ARFF format. Strings
		/// are quoted if they contain whitespace characters, or if they
		/// are a question mark.
		/// 
		/// </summary>
		/// <returns> the dataset in ARFF format as a string
		/// </returns>
		public override System.String ToString()
		{
			
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			
			text.Append(ARFF_RELATION).Append(" ").Append(Utils.quote(m_RelationName)).Append("\n\n");
			for (int i = 0; i < numAttributes(); i++)
			{
				text.Append(attribute(i)).Append("\n");
			}
			text.Append("\n").Append(ARFF_DATA).Append("\n");
			for (int i = 0; i < numInstances(); i++)
			{
				text.Append(instance(i));
				if (i < numInstances() - 1)
				{
					text.Append('\n');
				}
			}
			return text.ToString();
		}
		
		/// <summary> Creates the training set for one fold of a cross-validation 
		/// on the dataset. 
		/// 
		/// </summary>
		/// <param name="numFolds">the number of folds in the cross-validation. Must
		/// be greater than 1.
		/// </param>
		/// <param name="numFold">0 for the first fold, 1 for the second, ...
		/// </param>
		/// <returns> the training set 
		/// </returns>
		/// <exception cref="IllegalArgumentException">if the number of folds is less than 2
		/// or greater than the number of instances.
		/// </exception>
		//@ requires 2 <= numFolds && numFolds < numInstances();
		//@ requires 0 <= numFold && numFold < numFolds;
		public virtual Instances trainCV(int numFolds, int numFold)
		{
			
			int numInstForFold, first, offset;
			Instances train;
			
			if (numFolds < 2)
			{
				throw new System.ArgumentException("Number of folds must be at least 2!");
			}
			if (numFolds > numInstances())
			{
				throw new System.ArgumentException("Can't have more folds than instances!");
			}
			numInstForFold = numInstances() / numFolds;
			if (numFold < numInstances() % numFolds)
			{
				numInstForFold++;
				offset = numFold;
			}
			else
				offset = numInstances() % numFolds;
			train = new Instances(this, numInstances() - numInstForFold);
			first = numFold * (numInstances() / numFolds) + offset;
			copyInstances(0, train, first);
			copyInstances(first + numInstForFold, train, numInstances() - first - numInstForFold);
			
			return train;
		}
		
		/// <summary> Creates the training set for one fold of a cross-validation 
		/// on the dataset. The data is subsequently randomized based
		/// on the given random number generator.
		/// 
		/// </summary>
		/// <param name="numFolds">the number of folds in the cross-validation. Must
		/// be greater than 1.
		/// </param>
		/// <param name="numFold">0 for the first fold, 1 for the second, ...
		/// </param>
		/// <param name="random">the random number generator
		/// </param>
		/// <returns> the training set 
		/// </returns>
		/// <exception cref="IllegalArgumentException">if the number of folds is less than 2
		/// or greater than the number of instances.
		/// </exception>
		//@ requires 2 <= numFolds && numFolds < numInstances();
		//@ requires 0 <= numFold && numFold < numFolds;
		public virtual Instances trainCV(int numFolds, int numFold, System.Random random)
		{
			
			Instances train = trainCV(numFolds, numFold);
			train.randomize(random);
			return train;
		}
		
		/// <summary> Computes the variance for a numeric attribute.
		/// 
		/// </summary>
		/// <param name="attIndex">the numeric attribute
		/// </param>
		/// <returns> the variance if the attribute is numeric
		/// </returns>
		/// <exception cref="IllegalArgumentException">if the attribute is not numeric
		/// </exception>
		public virtual double variance(int attIndex)
		{
			
			double sum = 0, sumSquared = 0, sumOfWeights = 0;
			
			if (!attribute(attIndex).Numeric)
			{
				throw new System.ArgumentException("Can't compute variance because attribute is " + "not numeric!");
			}
			for (int i = 0; i < numInstances(); i++)
			{
				if (!instance(i).isMissing(attIndex))
				{
					sum += instance(i).weight() * instance(i).value_Renamed(attIndex);
					sumSquared += instance(i).weight() * instance(i).value_Renamed(attIndex) * instance(i).value_Renamed(attIndex);
					sumOfWeights += instance(i).weight();
				}
			}
			if (sumOfWeights <= 1)
			{
				return 0;
			}
			double result = (sumSquared - (sum * sum / sumOfWeights)) / (sumOfWeights - 1);
			
			// We don't like negative variance
			if (result < 0)
			{
				return 0;
			}
			else
			{
				return result;
			}
		}
		
		/// <summary> Computes the variance for a numeric attribute.
		/// 
		/// </summary>
		/// <param name="att">the numeric attribute
		/// </param>
		/// <returns> the variance if the attribute is numeric
		/// </returns>
		/// <exception cref="IllegalArgumentException">if the attribute is not numeric
		/// </exception>
		public virtual double variance(Attribute att)
		{
			
			return variance(att.index());
		}
		
		/// <summary> Calculates summary statistics on the values that appear in this
		/// set of instances for a specified attribute.
		/// 
		/// </summary>
		/// <param name="index">the index of the attribute to summarize.
		/// </param>
		/// <returns> an AttributeStats object with it's fields calculated.
		/// </returns>
		//@ requires 0 <= index && index < numAttributes();
		public virtual AttributeStats attributeStats(int index)
		{
			
			AttributeStats result = new AttributeStats();
			if (attribute(index).Nominal)
			{
				result.nominalCounts = new int[attribute(index).numValues()];
			}
			//if (attribute(index).Numeric)
			//{
		//		result.numericStats = new weka.experiment.Stats();
	//		}
			result.totalCount = numInstances();
			
			double[] attVals = attributeToDoubleArray(index);
			int[] sorted = Utils.sort(attVals);
			int currentCount = 0;
			double prev = Instance.missingValue();
			for (int j = 0; j < numInstances(); j++)
			{
				Instance current = instance(sorted[j]);
				if (current.isMissing(index))
				{
					result.missingCount = numInstances() - j;
					break;
				}
				if (current.value_Renamed(index) == prev)
				{
					currentCount++;
				}
				else
				{
					result.addDistinct(prev, currentCount);
					currentCount = 1;
					prev = current.value_Renamed(index);
				}
			}
			result.addDistinct(prev, currentCount);
			result.distinctCount--; // So we don't count "missing" as a value 
			return result;
		}
		
		/// <summary> Gets the value of all instances in this dataset for a particular
		/// attribute. Useful in conjunction with Utils.sort to allow iterating
		/// through the dataset in sorted order for some attribute.
		/// 
		/// </summary>
		/// <param name="index">the index of the attribute.
		/// </param>
		/// <returns> an array containing the value of the desired attribute for
		/// each instance in the dataset. 
		/// </returns>
		//@ requires 0 <= index && index < numAttributes();
		public virtual double[] attributeToDoubleArray(int index)
		{
			
			double[] result = new double[numInstances()];
			for (int i = 0; i < result.Length; i++)
			{
				result[i] = instance(i).value_Renamed(index);
			}
			return result;
		}
		
		/// <summary> Generates a string summarizing the set of instances. Gives a breakdown
		/// for each attribute indicating the number of missing/discrete/unique
		/// values and other information.
		/// 
		/// </summary>
		/// <returns> a string summarizing the dataset
		/// </returns>
		public virtual System.String toSummaryString()
		{
			
			System.Text.StringBuilder result = new System.Text.StringBuilder();
			result.Append("Relation Name:  ").Append(relationName()).Append("\r\n");
			result.Append("Num Instances:  ").Append(numInstances()).Append("\r\n");
            result.Append("Num Attributes: ").Append(numAttributes()).Append("\r\n");
            result.Append("\r\n");
			
			result.Append(Utils.padLeft("", 5)).Append(Utils.padRight("Name", 25));
			result.Append(Utils.padLeft("Type", 5)).Append(Utils.padLeft("Nom", 5));
			result.Append(Utils.padLeft("Int", 5)).Append(Utils.padLeft("Real", 5));
			result.Append(Utils.padLeft("Missing", 12));
			result.Append(Utils.padLeft("Unique", 12));
            result.Append(Utils.padLeft("Dist", 6)).Append("\r\n");
			for (int i = 0; i < numAttributes(); i++)
			{
				Attribute a = attribute(i);
				AttributeStats as_Renamed = attributeStats(i);
				result.Append(Utils.padLeft("" + (i + 1), 4)).Append(' ');
				result.Append(Utils.padRight(a.name(), 25)).Append(' ');
				long percent;
				switch (a.type())
				{
					
					case Attribute.NOMINAL: 
						result.Append(Utils.padLeft("Nom", 4)).Append(' ');
						//UPGRADE_TODO: Method 'java.lang.Math.round' was converted to 'System.Math.Round' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javalangMathround_double'"
						percent = (long) System.Math.Round(100.0 * as_Renamed.intCount / as_Renamed.totalCount);
						result.Append(Utils.padLeft("" + percent, 3)).Append("% ");
						result.Append(Utils.padLeft("" + 0, 3)).Append("% ");
						//UPGRADE_TODO: Method 'java.lang.Math.round' was converted to 'System.Math.Round' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javalangMathround_double'"
						percent = (long) System.Math.Round(100.0 * as_Renamed.realCount / as_Renamed.totalCount);
						result.Append(Utils.padLeft("" + percent, 3)).Append("% ");
						break;
					
					case Attribute.NUMERIC: 
						result.Append(Utils.padLeft("Num", 4)).Append(' ');
						result.Append(Utils.padLeft("" + 0, 3)).Append("% ");
						//UPGRADE_TODO: Method 'java.lang.Math.round' was converted to 'System.Math.Round' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javalangMathround_double'"
						percent = (long) System.Math.Round(100.0 * as_Renamed.intCount / as_Renamed.totalCount);
						result.Append(Utils.padLeft("" + percent, 3)).Append("% ");
						//UPGRADE_TODO: Method 'java.lang.Math.round' was converted to 'System.Math.Round' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javalangMathround_double'"
						percent = (long) System.Math.Round(100.0 * as_Renamed.realCount / as_Renamed.totalCount);
						result.Append(Utils.padLeft("" + percent, 3)).Append("% ");
						break;
					
					case Attribute.DATE: 
						result.Append(Utils.padLeft("Dat", 4)).Append(' ');
						result.Append(Utils.padLeft("" + 0, 3)).Append("% ");
						//UPGRADE_TODO: Method 'java.lang.Math.round' was converted to 'System.Math.Round' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javalangMathround_double'"
						percent = (long) System.Math.Round(100.0 * as_Renamed.intCount / as_Renamed.totalCount);
						result.Append(Utils.padLeft("" + percent, 3)).Append("% ");
						//UPGRADE_TODO: Method 'java.lang.Math.round' was converted to 'System.Math.Round' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javalangMathround_double'"
						percent = (long) System.Math.Round(100.0 * as_Renamed.realCount / as_Renamed.totalCount);
						result.Append(Utils.padLeft("" + percent, 3)).Append("% ");
						break;
					
					case Attribute.STRING: 
						result.Append(Utils.padLeft("Str", 4)).Append(' ');
						//UPGRADE_TODO: Method 'java.lang.Math.round' was converted to 'System.Math.Round' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javalangMathround_double'"
						percent = (long) System.Math.Round(100.0 * as_Renamed.intCount / as_Renamed.totalCount);
						result.Append(Utils.padLeft("" + percent, 3)).Append("% ");
						result.Append(Utils.padLeft("" + 0, 3)).Append("% ");
						//UPGRADE_TODO: Method 'java.lang.Math.round' was converted to 'System.Math.Round' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javalangMathround_double'"
						percent = (long) System.Math.Round(100.0 * as_Renamed.realCount / as_Renamed.totalCount);
						result.Append(Utils.padLeft("" + percent, 3)).Append("% ");
						break;
					
					default: 
						result.Append(Utils.padLeft("???", 4)).Append(' ');
						result.Append(Utils.padLeft("" + 0, 3)).Append("% ");
						//UPGRADE_TODO: Method 'java.lang.Math.round' was converted to 'System.Math.Round' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javalangMathround_double'"
						percent = (long) System.Math.Round(100.0 * as_Renamed.intCount / as_Renamed.totalCount);
						result.Append(Utils.padLeft("" + percent, 3)).Append("% ");
						//UPGRADE_TODO: Method 'java.lang.Math.round' was converted to 'System.Math.Round' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javalangMathround_double'"
						percent = (long) System.Math.Round(100.0 * as_Renamed.realCount / as_Renamed.totalCount);
						result.Append(Utils.padLeft("" + percent, 3)).Append("% ");
						break;
					
				}
				result.Append(Utils.padLeft("" + as_Renamed.missingCount, 5)).Append(" /");
				//UPGRADE_TODO: Method 'java.lang.Math.round' was converted to 'System.Math.Round' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javalangMathround_double'"
				percent = (long) System.Math.Round(100.0 * as_Renamed.missingCount / as_Renamed.totalCount);
				result.Append(Utils.padLeft("" + percent, 3)).Append("% ");
				result.Append(Utils.padLeft("" + as_Renamed.uniqueCount, 5)).Append(" /");
				//UPGRADE_TODO: Method 'java.lang.Math.round' was converted to 'System.Math.Round' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javalangMathround_double'"
				percent = (long) System.Math.Round(100.0 * as_Renamed.uniqueCount / as_Renamed.totalCount);
				result.Append(Utils.padLeft("" + percent, 3)).Append("% ");
				result.Append(Utils.padLeft("" + as_Renamed.distinctCount, 5)).Append(' ');
                result.Append("\r\n");
			}
			return result.ToString();
		}
		
		/// <summary> Reads a single instance using the tokenizer and appends it
		/// to the dataset. Automatically expands the dataset if it
		/// is not large enough to hold the instance.
		/// 
		/// </summary>
		/// <param name="tokenizer">the tokenizer to be used
		/// </param>
		/// <param name="flag">if method should test for carriage return after 
		/// each instance
		/// </param>
		/// <returns> false if end of file has been reached
		/// </returns>
		/// <exception cref="IOException">if the information is not read 
		/// successfully
		/// </exception>
		protected internal virtual bool getInstance(StreamTokenizer tokenizer, bool flag)
		{
			
			// Check if any attributes have been declared.
			if (m_Attributes.size() == 0)
			{
				errms(tokenizer, "no header information available");
			}
			
			// Check if end of file reached.
			//getFirstToken(tokenizer);
            Token token;

            getFirstToken(tokenizer, out token);
            tokenizer.PushBack(token);
          

			//if (tokenizer.ttype == SupportClass.StreamTokenizerSupport.TT_EOF)
            if (token is EofToken)
			{
				return false;
			}

            
			// Parse instance
			//if (tokenizer.ttype == '{')
            if ((token is CharToken) && (token.StringValue == "{"))
			{
				return getInstanceSparse(tokenizer, flag);
			}
			else
			{
				return getInstanceFull(tokenizer, flag);
			}
		}
		
		/// <summary> Reads a single instance using the tokenizer and appends it
		/// to the dataset. Automatically expands the dataset if it
		/// is not large enough to hold the instance.
		/// 
		/// </summary>
		/// <param name="tokenizer">the tokenizer to be used
		/// </param>
		/// <param name="flag">if method should test for carriage return after 
		/// each instance
		/// </param>
		/// <returns> false if end of file has been reached
		/// </returns>
		/// <exception cref="IOException">if the information is not read 
		/// successfully
		/// </exception>
		protected internal virtual bool getInstanceSparse(StreamTokenizer tokenizer, bool flag)
		{
			
			int valIndex, numValues = 0, maxIndex = - 1;
            Token token;
			// Get values
			do 
			{
             
				// Get index
				getIndex(tokenizer,out token);
				//if (tokenizer.ttype == '}')
                if ((token is CharToken) && (token.StringValue == "}"))
				{
					break;
				}
				
				// Is index valid?
				try
				{
					m_IndicesBuffer[numValues] = System.Int32.Parse(token.StringValue);
				}
				catch (System.FormatException e)
				{
					errms(tokenizer, "index number expected" + " "+e.ToString());
				}
				if (m_IndicesBuffer[numValues] <= maxIndex)
				{
					errms(tokenizer, "indices have to be ordered" );
				}
				if ((m_IndicesBuffer[numValues] < 0) || (m_IndicesBuffer[numValues] >= numAttributes()))
				{
					errms(tokenizer, "index out of bounds");
				}
				maxIndex = m_IndicesBuffer[numValues];
				
				// Get value;
                
				getNextToken(tokenizer,out token);
				
				// Check if value is missing.
				//if (tokenizer.ttype == '?')
                if ((token is CharToken) && (token.StringValue == "?"))
				{
					m_ValueBuffer[numValues] = Instance.missingValue();
				}
				else
				{
					
					// Check if token is valid.
                    if (!(token is WordToken))
					{
						errms(tokenizer, "not a valid value");
					}
					switch (attribute(m_IndicesBuffer[numValues]).type())
					{
						
						case Attribute.NOMINAL: 
							// Check if value appears in header.
							valIndex = attribute(m_IndicesBuffer[numValues]).indexOfValue(token.StringValue);
							if (valIndex == - 1)
							{
								errms(tokenizer, "nominal value not declared in header");
							}
							m_ValueBuffer[numValues] = (double) valIndex;
							break;
						
						case Attribute.NUMERIC: 
							// Check if value is really a number.
							try
							{
								m_ValueBuffer[numValues] = System.Double.Parse(token.StringValue);
							}
							catch (System.FormatException e)
							{
                                errms(tokenizer, "number expected" + " " + e.ToString());
							}
							break;
						
						case Attribute.STRING: 
							m_ValueBuffer[numValues] = attribute(m_IndicesBuffer[numValues]).addStringValue(token.StringValue);
							break;
						
						case Attribute.DATE: 
							try
							{
								m_ValueBuffer[numValues] = attribute(m_IndicesBuffer[numValues]).parseDate(token.StringValue);
							}
							//UPGRADE_TODO: Class 'java.text.ParseException' was converted to 'System.FormatException' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javatextParseException'"
							catch (System.FormatException e)
							{
								errms(tokenizer, "unparseable date: " + token.StringValue +" "+e.ToString());
							}
							break;
						
						default: 
							errms(tokenizer, "unknown attribute type in column " + m_IndicesBuffer[numValues]);
							break;
						
					}
				}
				numValues++;
			}
			while (true);
			if (flag)
			{
				getLastToken(tokenizer,out token, true);
			}
			
			// Add instance to dataset
			double[] tempValues = new double[numValues];
			int[] tempIndices = new int[numValues];
			Array.Copy(m_ValueBuffer, 0, tempValues, 0, numValues);
			Array.Copy(m_IndicesBuffer, 0, tempIndices, 0, numValues);
			add(new SparseInstance(1, tempValues, tempIndices, numAttributes()));
			return true;
		}
		
		/// <summary> Reads a single instance using the tokenizer and appends it
		/// to the dataset. Automatically expands the dataset if it
		/// is not large enough to hold the instance.
		/// 
		/// </summary>
		/// <param name="tokenizer">the tokenizer to be used
		/// </param>
		/// <param name="flag">if method should test for carriage return after 
		/// each instance
		/// </param>
		/// <returns> false if end of file has been reached
		/// </returns>
		/// <exception cref="IOException">if the information is not read 
		/// successfully
		/// </exception>
		protected internal virtual bool getInstanceFull(StreamTokenizer tokenizer, bool flag)
		{
			
			double[] instance = new double[numAttributes()];
			int index;
            Token token=null;

			// Get values for all attributes.
			for (int i = 0; i < numAttributes(); i++)
			{
				
				// Get next token
				//if (i > 0)
				//{
				getNextToken(tokenizer,out token);
				//}
				
				// Check if value is missing.
				//if (tokenizer.ttype == '?')
                if (token != null)
                {
                    if (token.StringValue == "?")
                    {
                        instance[i] = Instance.missingValue();
                    }
                    else
                    {

                        // Check if token is valid.
                        //if (tokenizer.ttype != SupportClass.StreamTokenizerSupport.TT_WORD)
                        if (!(token is WordToken))
                        {
                            errms(tokenizer, "not a valid value");
                        }
                        switch (attribute(i).type())
                        {

                            case Attribute.NOMINAL:
                                // Check if value appears in header.
                                index = attribute(i).indexOfValue(token.StringValue);
                                if (index == -1)
                                {
                                    errms(tokenizer, "nominal value not declared in header");
                                }
                                instance[i] = (double)index;
                                break;

                            case Attribute.NUMERIC:
                                // Check if value is really a number.
                                try
                                {
                                    instance[i] = System.Double.Parse(token.StringValue);
                                }
                                catch (System.FormatException e)
                                {
                                    errms(tokenizer, "number expected" + " " + e.ToString());
                                }
                                break;

                            case Attribute.STRING:
                                instance[i] = attribute(i).addStringValue(token.StringValue);
                                break;

                            case Attribute.DATE:
                                try
                                {
                                    instance[i] = attribute(i).parseDate(token.StringValue);
                                }
                                //UPGRADE_TODO: Class 'java.text.ParseException' was converted to 'System.FormatException' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javatextParseException'"
                                catch (System.FormatException e)
                                {
                                    errms(tokenizer, "unparseable date: " + token.StringValue + " " + e.ToString());
                                }
                                break;

                            default:
                                errms(tokenizer, "unknown attribute type in column " + i);
                                break;

                        }
                    }
                }
			}
			if (flag)
			{
				getLastToken(tokenizer,out token, true);
			}
			
			// Add instance to dataset
			add(new Instance(1, instance));
			return true;
		}
		
		/// <summary> Reads and stores header of an ARFF file.
		/// 
		/// </summary>
		/// <param name="tokenizer">the stream tokenizer
		/// </param>
		/// <exception cref="IOException">if the information is not read 
		/// successfully
		/// </exception>
		protected internal virtual void  readHeader(StreamTokenizer tokenizer)
		{
			
			System.String attributeName;
			FastVector attributeValues;
			//int i;
            Token token=null;
			// Get name of relation.
			getFirstToken(tokenizer, out token);
			//if (tokenizer.ttype == SupportClass.StreamTokenizerSupport.TT_EOF)
            if ((token != null)   && (token is EofToken))
			{
				errms(tokenizer, "premature end of file");
			}
			if (ARFF_RELATION.ToUpper().Equals(token.StringValue.ToUpper()))
			{
				getNextToken(tokenizer,out token);
				m_RelationName = token.StringValue;
				getLastToken(tokenizer,out token, false);
			}
			else
			{
				errms(tokenizer, "keyword " + ARFF_RELATION + " expected");
			}
			
			// Create vectors to hold information temporarily.
			m_Attributes = new FastVector();
			
			// Get attribute declarations.
			getFirstToken(tokenizer, out token);
			//if (tokenizer.ttype == SupportClass.StreamTokenizerSupport.TT_EOF)
            if ((token != null) && (token is EofToken))
			{
				errms(tokenizer, "premature end of file");
			}
			
			while (Attribute.ARFF_ATTRIBUTE.ToUpper().Equals(token.StringValue.ToUpper()))
			{
				
				// Get attribute name.
				getNextToken(tokenizer,out token);
				attributeName = token.StringValue;
				getNextToken(tokenizer,out token);
				
				// Check if attribute is nominal.
				//if (tokenizer.ttype == SupportClass.StreamTokenizerSupport.TT_WORD)
                if ((token != null) && (token is WordToken))
				{
					
					// Attribute is real, integer, or string.
                    if (token.StringValue.ToUpper().Equals(Attribute.ARFF_ATTRIBUTE_REAL.ToUpper()) || token.StringValue.ToUpper().Equals(Attribute.ARFF_ATTRIBUTE_INTEGER.ToUpper()) || token.StringValue.ToUpper().Equals(Attribute.ARFF_ATTRIBUTE_NUMERIC.ToUpper()))
					{
						m_Attributes.addElement(new Attribute(attributeName, numAttributes()));
						readTillEOL(tokenizer);
					}
                    else if (token.StringValue.ToUpper().Equals(Attribute.ARFF_ATTRIBUTE_STRING.ToUpper()))
					{
						m_Attributes.addElement(new Attribute(attributeName, (FastVector) null, numAttributes()));
						readTillEOL(tokenizer);
					}
                    else if (token.StringValue.ToUpper().Equals(Attribute.ARFF_ATTRIBUTE_DATE.ToUpper()))
					{
						System.String format = null;
                        tokenizer.NextToken(out token);
						//if (tokenizer.NextToken() != SupportClass.StreamTokenizerSupport.TT_EOL)
                        if ((token != null) && (!(token is EofToken)))
						{
							//if ((tokenizer.ttype != SupportClass.StreamTokenizerSupport.TT_WORD) && (tokenizer.ttype != '\'') && (tokenizer.ttype != '\"'))
                            if ((token != null) && (!(token is WordToken)) && (token.StringValue!="'") && (token.StringValue!="\"") )
							{
								errms(tokenizer, "not a valid date format");
							}
							format = token.StringValue;
							readTillEOL(tokenizer);
						}
						else
						{
							tokenizer.PushBack(token);
						}
						m_Attributes.addElement(new Attribute(attributeName, format, numAttributes()));
					}
					else
					{
						errms(tokenizer, "no valid attribute type or invalid " + "enumeration");
					}
				}
				else
				{
					
					// Attribute is nominal.
					attributeValues = new FastVector();
					tokenizer.PushBack(token);
					
					// Get values for nominal attribute.
                    tokenizer.NextToken(out token);
					if ( token.StringValue != "{")
					{
						errms(tokenizer, "{ expected at beginning of enumeration");
					}
                    tokenizer.NextToken(out token);
					while ( token.StringValue != "}")
					{
						//if (tokenizer.ttype == SupportClass.StreamTokenizerSupport.TT_EOL)
                        if (token is EolToken)
						{
							errms(tokenizer, "} expected at end of enumeration");
						}
						else
						{
							attributeValues.addElement(token.StringValue);
						}

                        tokenizer.NextToken(out token);
					}
					if (attributeValues.size() == 0)
					{
						errms(tokenizer, "no nominal values found");
					}
					m_Attributes.addElement(new Attribute(attributeName, attributeValues, numAttributes()));
				}
				getLastToken(tokenizer,out token, false);
				getFirstToken(tokenizer,out token);
				//if (tokenizer.ttype == SupportClass.StreamTokenizerSupport.TT_EOF)
                if (token is EofToken)
					errms(tokenizer, "premature end of file");
			}
			
			// Check if data part follows. We can't easily check for EOL.
			if (!ARFF_DATA.ToUpper().Equals(token.StringValue.ToUpper()))
			{
				errms(tokenizer, "keyword " + ARFF_DATA + " expected");
			}
			
			// Check if any attributes have been declared.
			if (m_Attributes.size() == 0)
			{
				errms(tokenizer, "no attributes declared");
			}
			
			// Allocate buffers in case sparse instances have to be read
			m_ValueBuffer = new double[numAttributes()];
			m_IndicesBuffer = new int[numAttributes()];
            
            
		}
		
		/// <summary> Copies instances from one set to the end of another 
		/// one.
		/// 
		/// </summary>
		/// <param name="source">the source of the instances
		/// </param>
		/// <param name="from">the position of the first instance to be copied
		/// </param>
		/// <param name="dest">the destination for the instances
		/// </param>
		/// <param name="num">the number of instances to be copied
		/// </param>
		//@ requires 0 <= from && from <= numInstances() - num;
		//@ requires 0 <= num;
		protected internal virtual void  copyInstances(int from, Instances dest, int num)
		{
			
			for (int i = 0; i < num; i++)
			{
				dest.add(instance(from + i));
			}
		}
		
		/// <summary> Throws error message with line number and last token read.
		/// 
		/// </summary>
		/// <param name="theMsg">the error message to be thrown
		/// </param>
		/// <param name="tokenizer">the stream tokenizer
		/// </param>
		/// <throws>  IOExcpetion containing the error message </throws>
		protected internal virtual void  errms(Token token, System.String theMsg)
		{
			
			throw new System.IO.IOException(theMsg + ", read " + token.ToString());
		}

        protected internal virtual void errms(StreamTokenizer tokenizer, System.String theMsg)
        {

            throw new System.IO.IOException(theMsg + ", read " + tokenizer.ToString());
        }
		
		/// <summary> Replaces the attribute information by a clone of
		/// itself.
		/// </summary>
		protected internal virtual void  freshAttributeInfo()
		{
			
			m_Attributes = (FastVector) m_Attributes.copyXmlElements();
		}
		
		/// <summary> Gets next token, skipping empty lines.
		/// 
		/// </summary>
		/// <param name="tokenizer">the stream tokenizer
		/// </param>
		/// <exception cref="IOException">if reading the next token fails
		/// </exception>
		protected internal virtual void  getFirstToken(StreamTokenizer tokenizer,out Token token)
		{
			
			//while (tokenizer.NextToken() == SupportClass.StreamTokenizerSupport.TT_EOL)
            tokenizer.NextToken(out token);
            while(token is EolToken)
			{
                tokenizer.NextToken(out token);
			} ;

			//if ((tokenizer.ttype == '\'') || (tokenizer.ttype == '"'))
            //if ((token.StringValue == "'") || (token.StringValue == "\"") )
			//{
				//tokenizer.ttype = SupportClass.StreamTokenizerSupport.TT_WORD;
			//}
			//else if ((tokenizer.ttype == SupportClass.StreamTokenizerSupport.TT_WORD) && (tokenizer.sval.Equals("?")))
			//{
			//	tokenizer.ttype = '?';
			//}
		}
		
		/// <summary> Gets index, checking for a premature and of line.
		/// 
		/// </summary>
		/// <param name="tokenizer">the stream tokenizer
		/// </param>
		/// <exception cref="IOException">if it finds a premature end of line
		/// </exception>
		protected internal virtual void  getIndex(StreamTokenizer tokenizer, out Token token)
		{
			tokenizer.NextToken(out token);
            if (token is EolToken)
			{
				errms(tokenizer, "premature end of line");
			}
            if (token is EofToken)
			{
				errms(tokenizer, "premature end of file");
			}
		}
		
		/// <summary> Gets token and checks if its end of line.
		/// 
		/// </summary>
		/// <param name="tokenizer">the stream tokenizer
		/// </param>
		/// <exception cref="IOException">if it doesn't find an end of line
		/// </exception>
		protected internal virtual void  getLastToken(StreamTokenizer tokenizer,out Token token , bool endOfFileOk)
		{
			tokenizer.NextToken(out token);
			if ( (!(token is EolToken)) && ( (!(token is EofToken))  || !endOfFileOk))
			{
				errms(tokenizer, "end of line expected");
			}
		}
		
		/// <summary> Gets next token, checking for a premature and of line.
		/// 
		/// </summary>
		/// <param name="tokenizer">the stream tokenizer
		/// </param>
		/// <exception cref="IOException">if it finds a premature end of line
		/// </exception>
		protected internal virtual void  getNextToken(StreamTokenizer tokenizer,out Token token)
		{
            tokenizer.NextToken(out token);
			if (token is EolToken)
			{
				errms(tokenizer, "premature end of line");
			}
            if (token is EofToken)
			{
				errms(tokenizer, "premature end of file");
			}
			//else if ((tokenizer.ttype == '\'') || (tokenizer.ttype == '"'))
            else if ((token is CharToken) && ((token.StringValue == "'") || (token.StringValue == "\"") ))
			{
				//tokenizer.ttype = SupportClass.StreamTokenizerSupport.TT_WORD;
			}
			//else if ((tokenizer.ttype == SupportClass.StreamTokenizerSupport.TT_WORD) && (tokenizer.sval.Equals("?")))
            else if ((token is CharToken) && (token.StringValue == "?"))
			{
				//tokenizer.ttype = '?';
			}
		}
		
		/// <summary> Initializes the StreamTokenizer used for reading the ARFF file.
		/// 
		/// </summary>
		/// <param name="tokenizer">the stream tokenizer
		/// </param>
		protected internal virtual void  initTokenizer(StreamTokenizer tokenizer)
		{
			
			tokenizer.Settings.ResetCharTypeTable();
			tokenizer.Settings.WhitespaceChars(0,(int) ' ');
			tokenizer.Settings.WordChars((int)' ' + 1, (int) '\u00FF');
			tokenizer.Settings.WhitespaceChars((int)',',(int) ',');
			tokenizer.Settings.CommentChar('%');
			tokenizer.Settings.QuoteChar('"');
			tokenizer.Settings.QuoteChar('\'');
			tokenizer.Settings.OrdinaryChar('{');
			tokenizer.Settings.OrdinaryChar('}');
			tokenizer.Settings.GrabEol=true;
		}
		
		/// <summary> Returns string including all instances, their weights and
		/// their indices in the original dataset.
		/// 
		/// </summary>
		/// <returns> description of instance and its weight as a string
		/// </returns>
		protected internal virtual System.String instancesAndWeights()
		{
			
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			
			for (int i = 0; i < numInstances(); i++)
			{
				text.Append(instance(i) + " " + instance(i).weight());
				if (i < numInstances() - 1)
				{
					text.Append("\n");
				}
			}
			return text.ToString();
		}
		
		/// <summary> Partitions the instances around a pivot. Used by quicksort and
		/// kthSmallestValue.
		/// 
		/// </summary>
		/// <param name="attIndex">the attribute's index
		/// </param>
		/// <param name="left">the first index of the subset 
		/// </param>
		/// <param name="right">the last index of the subset 
		/// 
		/// </param>
		/// <returns> the index of the middle element
		/// </returns>
		//@ requires 0 <= attIndex && attIndex < numAttributes();
		//@ requires 0 <= left && left <= right && right < numInstances();
		protected internal virtual int partition(int attIndex, int l, int r)
		{
			
			double pivot = instance((l + r) / 2).value_Renamed(attIndex);
			
			while (l < r)
			{
				while ((instance(l).value_Renamed(attIndex) < pivot) && (l < r))
				{
					l++;
				}
				while ((instance(r).value_Renamed(attIndex) > pivot) && (l < r))
				{
					r--;
				}
				if (l < r)
				{
					swap(l, r);
					l++;
					r--;
				}
			}
			if ((l == r) && (instance(r).value_Renamed(attIndex) > pivot))
			{
				r--;
			}
			
			return r;
		}
		
		/// <summary> Implements quicksort according to Manber's "Introduction to
		/// Algorithms".
		/// 
		/// </summary>
		/// <param name="attIndex">the attribute's index
		/// </param>
		/// <param name="left">the first index of the subset to be sorted
		/// </param>
		/// <param name="right">the last index of the subset to be sorted
		/// </param>
		//@ requires 0 <= attIndex && attIndex < numAttributes();
		//@ requires 0 <= first && first <= right && right < numInstances();
		protected internal virtual void  quickSort(int attIndex, int left, int right)
		{
			
			if (left < right)
			{
				int middle = partition(attIndex, left, right);
				quickSort(attIndex, left, middle);
				quickSort(attIndex, middle + 1, right);
			}
		}
		
		/// <summary> Reads and skips all tokens before next end of line token.
		/// 
		/// </summary>
		/// <param name="tokenizer">the stream tokenizer
		/// </param>
		protected internal virtual void  readTillEOL(StreamTokenizer tokenizer)
		{

            Token token;
            tokenizer.NextToken(out token);
			while (!(token is EolToken))
			{
                tokenizer.NextToken(out token);
			} ;
			tokenizer.PushBack(token);
		}
		
		/// <summary> Implements computation of the kth-smallest element according
		/// to Manber's "Introduction to Algorithms".
		/// 
		/// </summary>
		/// <param name="attIndex">the attribute's index
		/// </param>
		/// <param name="left">the first index of the subset 
		/// </param>
		/// <param name="right">the last index of the subset 
		/// </param>
		/// <param name="k">the value of k
		/// 
		/// </param>
		/// <returns> the index of the kth-smallest element
		/// </returns>
		//@ requires 0 <= attIndex && attIndex < numAttributes();
		//@ requires 0 <= first && first <= right && right < numInstances();
		protected internal virtual int select(int attIndex, int left, int right, int k)
		{
			
			if (left == right)
			{
				return left;
			}
			else
			{
				int middle = partition(attIndex, left, right);
				if ((middle - left + 1) >= k)
				{
					return select(attIndex, left, middle, k);
				}
				else
				{
					return select(attIndex, middle + 1, right, k - (middle - left + 1));
				}
			}
		}
		
		/// <summary> Help function needed for stratification of set.
		/// 
		/// </summary>
		/// <param name="numFolds">the number of folds for the stratification
		/// </param>
		protected internal virtual void  stratStep(int numFolds)
		{
			
			FastVector newVec = new FastVector(m_Instances.capacity());
			int start = 0, j;
			
			// create stratified batch
			while (newVec.size() < numInstances())
			{
				j = start;
				while (j < numInstances())
				{
					newVec.addElement(instance(j));
					j = j + numFolds;
				}
				start++;
			}
			m_Instances = newVec;
		}
		
		/// <summary> Swaps two instances in the set.
		/// 
		/// </summary>
		/// <param name="i">the first instance's index
		/// </param>
		/// <param name="j">the second instance's index
		/// </param>
		//@ requires 0 <= i && i < numInstances();
		//@ requires 0 <= j && j < numInstances();
		public virtual void  swap(int i, int j)
		{
			
			m_Instances.swap(i, j);
		}
		
		/// <summary> Merges two sets of Instances together. The resulting set will have
		/// all the attributes of the first set plus all the attributes of the 
		/// second set. The number of instances in both sets must be the same.
		/// 
		/// </summary>
		/// <param name="first">the first set of Instances
		/// </param>
		/// <param name="second">the second set of Instances
		/// </param>
		/// <returns> the merged set of Instances
		/// </returns>
		/// <exception cref="IllegalArgumentException">if the datasets are not the same size
		/// </exception>
		public static Instances mergeInstances(Instances first, Instances second)
		{
			
			if (first.numInstances() != second.numInstances())
			{
				throw new System.ArgumentException("Instance sets must be of the same size");
			}
			
			// Create the vector of merged attributes
			FastVector newAttributes = new FastVector();
			for (int i = 0; i < first.numAttributes(); i++)
			{
				newAttributes.addElement(first.attribute(i));
			}
			for (int i = 0; i < second.numAttributes(); i++)
			{
				newAttributes.addElement(second.attribute(i));
			}
			
			// Create the set of Instances
			Instances merged = new Instances(first.relationName() + '_' + second.relationName(), newAttributes, first.numInstances());
			// Merge each instance
			for (int i = 0; i < first.numInstances(); i++)
			{
				merged.add(first.instance(i).mergeInstance(second.instance(i)));
			}
			return merged;
		}
		
		/// <summary> Method for testing this class.
		/// 
		/// </summary>
		/// <param name="argv">should contain one element: the name of an ARFF file
		/// </param>
		//@ requires argv != null;
		//@ requires argv.length == 1;
		//@ requires argv[0] != null;
		public static void  test(System.String[] argv)
		{
			
			Instances instances, secondInstances, train, test, empty;
			//Instance instance;
			//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.util.Random.Random'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
			System.Random random = new System.Random((System.Int32) 2);
			//UPGRADE_ISSUE: Class hierarchy differences between 'java.io.Reader' and 'System.IO.StreamReader' may cause compilation errors. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1186'"
			System.IO.StreamReader reader;
			int start, num;
			//double newWeight;
			FastVector testAtts, testVals;
			int i, j;
			
			try
			{
				if (argv.Length > 1)
				{
					throw (new System.Exception("Usage: Instances [<filename>]"));
				}
				
				// Creating set of instances from scratch
				testVals = new FastVector(2);
				testVals.addElement("first_value");
				testVals.addElement("second_value");
				testAtts = new FastVector(2);
				testAtts.addElement(new Attribute("nominal_attribute", testVals));
				testAtts.addElement(new Attribute("numeric_attribute"));
				instances = new Instances("test_set", testAtts, 10);
				instances.add(new Instance(instances.numAttributes()));
				instances.add(new Instance(instances.numAttributes()));
				instances.add(new Instance(instances.numAttributes()));
				instances.ClassIndex = 0;
				System.Console.Out.WriteLine("\nSet of instances created from scratch:\n");
				//UPGRADE_TODO: Method 'java.io.PrintStream.println' was converted to 'System.Console.Out.WriteLine' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioPrintStreamprintln_javalangObject'"
				System.Console.Out.WriteLine(instances);
				
				if (argv.Length == 1)
				{
					System.String filename = argv[0];
					//UPGRADE_TODO: Constructor 'java.io.FileReader.FileReader' was converted to 'System.IO.StreamReader' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073'"
					reader = new System.IO.StreamReader(filename, System.Text.Encoding.Default);
					
					// Read first five instances and print them
					System.Console.Out.WriteLine("\nFirst five instances from file:\n");
					instances = new Instances(reader, 1);
					instances.ClassIndex = instances.numAttributes() - 1;
					i = 0;
					while ((i < 5) && (instances.readInstance(reader)))
					{
						i++;
					}
					//UPGRADE_TODO: Method 'java.io.PrintStream.println' was converted to 'System.Console.Out.WriteLine' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioPrintStreamprintln_javalangObject'"
					System.Console.Out.WriteLine(instances);
					
					// Read all the instances in the file
					//UPGRADE_TODO: Constructor 'java.io.FileReader.FileReader' was converted to 'System.IO.StreamReader' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073'"
					reader = new System.IO.StreamReader(filename, System.Text.Encoding.Default);
					instances = new Instances(reader);
					
					// Make the last attribute be the class 
					instances.ClassIndex = instances.numAttributes() - 1;
					
					// Print header and instances.
					System.Console.Out.WriteLine("\nDataset:\n");
					//UPGRADE_TODO: Method 'java.io.PrintStream.println' was converted to 'System.Console.Out.WriteLine' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioPrintStreamprintln_javalangObject'"
					System.Console.Out.WriteLine(instances);
					System.Console.Out.WriteLine("\nClass index: " + instances.classIndex());
				}
				
				// Test basic methods based on class index.
				System.Console.Out.WriteLine("\nClass name: " + instances.classAttribute().name());
				System.Console.Out.WriteLine("\nClass index: " + instances.classIndex());
				System.Console.Out.WriteLine("\nClass is nominal: " + instances.classAttribute().Nominal);
				System.Console.Out.WriteLine("\nClass is numeric: " + instances.classAttribute().Numeric);
				System.Console.Out.WriteLine("\nClasses:\n");
				for (i = 0; i < instances.numClasses(); i++)
				{
					System.Console.Out.WriteLine(instances.classAttribute().value_Renamed(i));
				}
				System.Console.Out.WriteLine("\nClass values and labels of instances:\n");
				for (i = 0; i < instances.numInstances(); i++)
				{
					Instance inst = instances.instance(i);
					System.Console.Out.Write(inst.classValue() + "\t");
					System.Console.Out.Write(inst.toString(inst.classIndex()));
					if (instances.instance(i).classIsMissing())
					{
						System.Console.Out.WriteLine("\tis missing");
					}
					else
					{
						System.Console.Out.WriteLine();
					}
				}
				
				// Create random weights.
				System.Console.Out.WriteLine("\nCreating random weights for instances.");
				for (i = 0; i < instances.numInstances(); i++)
				{
					instances.instance(i).Weight = random.NextDouble();
				}
				
				// Print all instances and their weights (and the sum of weights).
				System.Console.Out.WriteLine("\nInstances and their weights:\n");
				System.Console.Out.WriteLine(instances.instancesAndWeights());
				System.Console.Out.Write("\nSum of weights: ");
				System.Console.Out.WriteLine(instances.sumOfWeights());
				
				// Insert an attribute
				secondInstances = new Instances(instances);
				Attribute testAtt = new Attribute("Inserted");
				secondInstances.insertAttributeAt(testAtt, 0);
				System.Console.Out.WriteLine("\nSet with inserted attribute:\n");
				//UPGRADE_TODO: Method 'java.io.PrintStream.println' was converted to 'System.Console.Out.WriteLine' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioPrintStreamprintln_javalangObject'"
				System.Console.Out.WriteLine(secondInstances);
				System.Console.Out.WriteLine("\nClass name: " + secondInstances.classAttribute().name());
				
				// Delete the attribute
				secondInstances.deleteAttributeAt(0);
				System.Console.Out.WriteLine("\nSet with attribute deleted:\n");
				//UPGRADE_TODO: Method 'java.io.PrintStream.println' was converted to 'System.Console.Out.WriteLine' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioPrintStreamprintln_javalangObject'"
				System.Console.Out.WriteLine(secondInstances);
				System.Console.Out.WriteLine("\nClass name: " + secondInstances.classAttribute().name());
				
				// Test if headers are equal
				System.Console.Out.WriteLine("\nHeaders equal: " + instances.equalHeaders(secondInstances) + "\n");
				
				// Print data in internal format.
				System.Console.Out.WriteLine("\nData (internal values):\n");
				for (i = 0; i < instances.numInstances(); i++)
				{
					for (j = 0; j < instances.numAttributes(); j++)
					{
						if (instances.instance(i).isMissing(j))
						{
							System.Console.Out.Write("? ");
						}
						else
						{
							System.Console.Out.Write(instances.instance(i).value_Renamed(j) + " ");
						}
					}
					System.Console.Out.WriteLine();
				}
				
				// Just print header
				System.Console.Out.WriteLine("\nEmpty dataset:\n");
				empty = new Instances(instances, 0);
				//UPGRADE_TODO: Method 'java.io.PrintStream.println' was converted to 'System.Console.Out.WriteLine' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioPrintStreamprintln_javalangObject'"
				System.Console.Out.WriteLine(empty);
				System.Console.Out.WriteLine("\nClass name: " + empty.classAttribute().name());
				
				// Create copy and rename an attribute and a value (if possible)
				if (empty.classAttribute().Nominal)
				{
					Instances copy = new Instances(empty, 0);
					copy.renameAttribute(copy.classAttribute(), "new_name");
					copy.renameAttributeValue(copy.classAttribute(), copy.classAttribute().value_Renamed(0), "new_val_name");
					System.Console.Out.WriteLine("\nDataset with names changed:\n" + copy);
					System.Console.Out.WriteLine("\nOriginal dataset:\n" + empty);
				}
				
				// Create and prints subset of instances.
				start = instances.numInstances() / 4;
				num = instances.numInstances() / 2;
				System.Console.Out.Write("\nSubset of dataset: ");
				System.Console.Out.WriteLine(num + " instances from " + (start + 1) + ". instance");
				secondInstances = new Instances(instances, start, num);
				System.Console.Out.WriteLine("\nClass name: " + secondInstances.classAttribute().name());
				
				// Print all instances and their weights (and the sum of weights).
				System.Console.Out.WriteLine("\nInstances and their weights:\n");
				System.Console.Out.WriteLine(secondInstances.instancesAndWeights());
				System.Console.Out.Write("\nSum of weights: ");
				System.Console.Out.WriteLine(secondInstances.sumOfWeights());
				
				// Create and print training and test sets for 3-fold
				// cross-validation.
				System.Console.Out.WriteLine("\nTrain and test folds for 3-fold CV:");
				if (instances.classAttribute().Nominal)
				{
					instances.stratify(3);
				}
				for (j = 0; j < 3; j++)
				{
					//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.util.Random.Random'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
					train = instances.trainCV(3, j, new System.Random((System.Int32) 1));
					test = instances.testCV(3, j);
					
					// Print all instances and their weights (and the sum of weights).
					System.Console.Out.WriteLine("\nTrain: ");
					System.Console.Out.WriteLine("\nInstances and their weights:\n");
					System.Console.Out.WriteLine(train.instancesAndWeights());
					System.Console.Out.Write("\nSum of weights: ");
					System.Console.Out.WriteLine(train.sumOfWeights());
					System.Console.Out.WriteLine("\nClass name: " + train.classAttribute().name());
					System.Console.Out.WriteLine("\nTest: ");
					System.Console.Out.WriteLine("\nInstances and their weights:\n");
					System.Console.Out.WriteLine(test.instancesAndWeights());
					System.Console.Out.Write("\nSum of weights: ");
					System.Console.Out.WriteLine(test.sumOfWeights());
					System.Console.Out.WriteLine("\nClass name: " + test.classAttribute().name());
				}
				
				// Randomize instances and print them.
				System.Console.Out.WriteLine("\nRandomized dataset:");
				instances.randomize(random);
				
				// Print all instances and their weights (and the sum of weights).
				System.Console.Out.WriteLine("\nInstances and their weights:\n");
				System.Console.Out.WriteLine(instances.instancesAndWeights());
				System.Console.Out.Write("\nSum of weights: ");
				System.Console.Out.WriteLine(instances.sumOfWeights());
				
				// Sort instances according to first attribute and
				// print them.
				System.Console.Out.Write("\nInstances sorted according to first attribute:\n ");
				instances.sort(0);
				
				// Print all instances and their weights (and the sum of weights).
				System.Console.Out.WriteLine("\nInstances and their weights:\n");
				System.Console.Out.WriteLine(instances.instancesAndWeights());
				System.Console.Out.Write("\nSum of weights: ");
				System.Console.Out.WriteLine(instances.sumOfWeights());
			}
			catch (System.Exception)
			{
				//.WriteStackTrace(e, Console.Error);
			}
		}
		
		/// <summary> Main method for this class. The following calls are possible:
		/// <ul>
		/// <li>
		/// <code>weka.core.Instances</code> &lt;filename&gt;<br/>
		/// prints a summary of a set of instances.
		/// </li>
		/// <li>
		/// <code>weka.core.Instances</code> merge &lt;filename1&gt; &lt;filename2&gt;<br/>
		/// merges the two datasets (must have same number of instances) and
		/// outputs the results on stdout.
		/// </li>
		/// </ul>
		/// 
		/// </summary>
		/// <param name="args">	the commandline parameters
		/// </param>
		//	public static void main(String[] args) 
		//	{
		//		try 
		//		{
		//			Instances i;
		//			// read from stdin and print statistics
		//			if (args.length == 0) 
		//			{
		//				i = new Instances(new BufferedReader(new InputStreamReader(System.in)));
		//				System.out.println(i.toSummaryString());
		//			}
		//				// read file and print statistics
		//			else if (args.length == 1) 
		//			{
		//				i = new Instances(new BufferedReader(new FileReader(args[0])));
		//				System.out.println(i.toSummaryString());
		//			}
		//				// read two files, merge them and print result to stdout
		//			else if ((args.length == 3) && (args[0].toLowerCase().equals("merge"))) 
		//			{
		//				i = Instances.mergeInstances(
		//					new Instances(new BufferedReader(new FileReader(args[1]))),
		//					new Instances(new BufferedReader(new FileReader(args[2]))));
		//				System.out.println(i);
		//			}
		//				// wrong parameters
		//			else 
		//			{
		//				System.err.println(
		//					"\nUsage:\n"
		//					+ "\tweka.core.Instances <filename>\n"
		//					+ "\tweka.core.Instances merge <filename1> <filename2>\n");
		//				System.exit(1);
		//			}
		//		}
		//		catch (Exception ex) 
		//		{
		//			ex.printStackTrace();
		//			System.err.println(ex.getMessage());
		//		}
		//	}
	}
}