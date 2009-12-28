/*
*    Instance.java
*    Copyright (C) 1999 Eibe Frank
*
*/
using System;
namespace weka.core
{
	
	/// <summary> Class for handling an instance. All values (numeric, date, nominal, or
	/// string) are internally stored as floating-point numbers. If an
	/// attribute is nominal (or a string), the stored value is the index
	/// of the corresponding nominal (or string) value in the attribute's
	/// definition. We have chosen this approach in favor of a more elegant
	/// object-oriented approach because it is much faster. <p>
	/// 
	/// Typical usage (code from the main() method of this class): <p>
	/// 
	/// <code>
	/// ... <br>
	/// 
	/// // Create empty instance with three attribute values <br>
	/// Instance inst = new Instance(3); <br><br>
	/// 
	/// // Set instance's values for the attributes "length", "weight", and "position"<br>
	/// inst.setValue(length, 5.3); <br>
	/// inst.setValue(weight, 300); <br>
	/// inst.setValue(position, "first"); <br><br>
	/// 
	/// // Set instance's dataset to be the dataset "race" <br>
	/// inst.setDataset(race); <br><br>
	/// 
	/// // Print the instance <br>
	/// System.out.println("The instance: " + inst); <br>
	/// 
	/// ... <br>
	/// </code><p>
	/// 
	/// All methods that change an instance are safe, ie. a change of an
	/// instance does not affect any other instances. All methods that
	/// change an instance's attribute values clone the attribute value
	/// vector before it is changed. If your application heavily modifies
	/// instance values, it may be faster to create a new instance from scratch.
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.19.2.2 $ 
	/// </version>

	public class Instance : Copyable
	{
		/// <summary> Sets the reference to the dataset. Does not check if the instance
		/// is compatible with the dataset. Note: the dataset does not know
		/// about this instance. If the structure of the dataset's header
		/// gets changed, this instance will not be adjusted automatically.
		/// 
		/// </summary>
		/// <param name="instances">the reference to the dataset 
		/// </param>
		virtual public Instances Dataset
		{
			set
			{
				
				m_Dataset = value;
			}
			
		}
		/// <summary> Sets the weight of an instance.
		/// 
		/// </summary>
		/// <param name="weight">the weight
		/// </param>
		virtual public double Weight
		{
			set
			{
				
				m_Weight = value;
			}
			
		}
		/// <summary>Constant representing a missing value. </summary>
		//UPGRADE_NOTE: Final was removed from the declaration of 'MISSING_VALUE '. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1003'"
		protected internal static readonly double MISSING_VALUE = System.Double.NaN;
		
		/// <summary> The dataset the instance has access to.  Null if the instance
		/// doesn't have access to any dataset.  Only if an instance has
		/// access to a dataset, it knows about the actual attribute types.  
		/// </summary>
		protected internal Instances m_Dataset;
		
		/// <summary>The instance's attribute values. </summary>
		protected internal double[] m_AttValues;
		
		/// <summary>The instance's weight. </summary>
		protected internal double m_Weight;
		
		/// <summary> Constructor that copies the attribute values and the weight from
		/// the given instance. Reference to the dataset is set to null.
		/// (ie. the instance doesn't have access to information about the
		/// attribute types)
		/// 
		/// </summary>
		/// <param name="instance">the instance from which the attribute
		/// values and the weight are to be copied 
		/// </param>
		//@ ensures m_Dataset == null;
		protected internal Instance(Instance instance)
		{
			
			m_AttValues = instance.m_AttValues;
			m_Weight = instance.m_Weight;
			m_Dataset = null;
		}
		
		/// <summary> Constructor that inititalizes instance variable with given
		/// values. Reference to the dataset is set to null. (ie. the instance
		/// doesn't have access to information about the attribute types)
		/// 
		/// </summary>
		/// <param name="weight">the instance's weight
		/// </param>
		/// <param name="attValues">a vector of attribute values 
		/// </param>
		//@ ensures m_Dataset == null;
		public Instance(double weight, double[] attValues)
		{
			
			m_AttValues = attValues;
			m_Weight = weight;
			m_Dataset = null;
		}
		
		/// <summary> Constructor of an instance that sets weight to one, all values to
		/// be missing, and the reference to the dataset to null. (ie. the instance
		/// doesn't have access to information about the attribute types)
		/// 
		/// </summary>
		/// <param name="numAttributes">the size of the instance 
		/// </param>
		//@ requires numAttributes > 0;    // Or maybe == 0 is okay too?
		//@ ensures m_Dataset == null;
		public Instance(int numAttributes)
		{
			
			m_AttValues = new double[numAttributes];
			for (int i = 0; i < m_AttValues.Length; i++)
			{
				m_AttValues[i] = MISSING_VALUE;
			}
			m_Weight = 1;
			m_Dataset = null;
		}
		
		/// <summary> Returns the attribute with the given index.
		/// 
		/// </summary>
		/// <param name="index">the attribute's index
		/// </param>
		/// <returns> the attribute at the given position
		/// </returns>
		/// <exception cref="Exception">if instance doesn't have access to a
		/// dataset
		/// </exception>
		//@ requires m_Dataset != null;
		public virtual Attribute attribute(int index)
		{
			
			if (m_Dataset == null)
			{
				throw new Exception("Instance doesn't have access to a dataset!");
			}
			return m_Dataset.attribute(index);
		}
		
		/// <summary> Returns the attribute with the given index. Does the same
		/// thing as attribute().
		/// 
		/// </summary>
		/// <param name="indexOfIndex">the index of the attribute's index 
		/// </param>
		/// <returns> the attribute at the given position
		/// </returns>
		/// <exception cref="Exception">if instance doesn't have access to a
		/// dataset
		/// </exception>
		//@ requires m_Dataset != null;
		public virtual Attribute attributeSparse(int indexOfIndex)
		{
			
			if (m_Dataset == null)
			{
				throw new Exception("Instance doesn't have access to a dataset!");
			}
			return m_Dataset.attribute(indexOfIndex);
		}
		
		/// <summary> Returns class attribute.
		/// 
		/// </summary>
		/// <returns> the class attribute
		/// </returns>
		/// <exception cref="Exception">if the class is not set or the
		/// instance doesn't have access to a dataset
		/// </exception>
		//@ requires m_Dataset != null;
		public virtual Attribute classAttribute()
		{
			
			if (m_Dataset == null)
			{
				throw new Exception("Instance doesn't have access to a dataset!");
			}
			return m_Dataset.classAttribute();
		}
		
		/// <summary> Returns the class attribute's index.
		/// 
		/// </summary>
		/// <returns> the class index as an integer 
		/// </returns>
		/// <exception cref="Exception">if instance doesn't have access to a dataset 
		/// </exception>
		//@ requires m_Dataset != null;
		//@ ensures  \result == m_Dataset.classIndex();
		public virtual int classIndex()
		{
			
			if (m_Dataset == null)
			{
				throw new Exception("Instance doesn't have access to a dataset!");
			}
			return m_Dataset.classIndex();
		}
		
		/// <summary> Tests if an instance's class is missing.
		/// 
		/// </summary>
		/// <returns> true if the instance's class is missing
		/// </returns>
		/// <exception cref="Exception">if the class is not set or the instance doesn't
		/// have access to a dataset
		/// </exception>
		//@ requires classIndex() >= 0;
		public virtual bool classIsMissing()
		{
			
			if (classIndex() < 0)
			{
				throw new Exception("Class is not set!");
			}
			return isMissing(classIndex());
		}
		
		/// <summary> Returns an instance's class value in internal format. (ie. as a
		/// floating-point number)
		/// 
		/// </summary>
		/// <returns> the corresponding value as a double (If the 
		/// corresponding attribute is nominal (or a string) then it returns the 
		/// value's index as a double).
		/// </returns>
		/// <exception cref="Exception">if the class is not set or the instance doesn't
		/// have access to a dataset 
		/// </exception>
		//@ requires classIndex() >= 0;
		public virtual double classValue()
		{
			
			if (classIndex() < 0)
			{
				throw new Exception("Class is not set!");
			}
			return value_Renamed(classIndex());
		}
		
		/// <summary> Produces a shallow copy of this instance. The copy has
		/// access to the same dataset. (if you want to make a copy
		/// that doesn't have access to the dataset, use 
		/// <code>new Instance(instance)</code>
		/// 
		/// </summary>
		/// <returns> the shallow copy
		/// </returns>
		//@ also ensures \result != null;
		//@ also ensures \result instanceof Instance;
		//@ also ensures ((Instance)\result).m_Dataset == m_Dataset;
		public virtual System.Object copy()
		{
			
			Instance result = new Instance(this);
			result.m_Dataset = m_Dataset;
			return result;
		}
		
		/// <summary> Returns the dataset this instance has access to. (ie. obtains
		/// information about attribute types from) Null if the instance
		/// doesn't have access to a dataset.
		/// 
		/// </summary>
		/// <returns> the dataset the instance has accesss to
		/// </returns>
		//@ ensures \result == m_Dataset;
		public virtual Instances dataset()
		{
			
			return m_Dataset;
		}
		
		/// <summary> Deletes an attribute at the given position (0 to 
		/// numAttributes() - 1). Only succeeds if the instance does not
		/// have access to any dataset because otherwise inconsistencies
		/// could be introduced.
		/// 
		/// </summary>
		/// <param name="pos">the attribute's position
		/// </param>
		/// <exception cref="RuntimeException">if the instance has access to a
		/// dataset 
		/// </exception>
		//@ requires m_Dataset != null;
		public virtual void  deleteAttributeAt(int position)
		{
			
			if (m_Dataset != null)
			{
				throw new System.SystemException("Instance has access to a dataset!");
			}
			forceDeleteAttributeAt(position);
		}
		
		/// <summary> Returns an enumeration of all the attributes.
		/// 
		/// </summary>
		/// <returns> enumeration of all the attributes
		/// </returns>
		/// <exception cref="Exception">if the instance doesn't
		/// have access to a dataset 
		/// </exception>
		//@ requires m_Dataset != null;
		public virtual System.Collections.IEnumerator enumerateAttributes()
		{
			
			if (m_Dataset == null)
			{
				throw new Exception("Instance doesn't have access to a dataset!");
			}
			return m_Dataset.enumerateAttributes();
		}
		
		/// <summary> Tests if the headers of two instances are equivalent.
		/// 
		/// </summary>
		/// <param name="instance">another instance
		/// </param>
		/// <returns> true if the header of the given instance is 
		/// equivalent to this instance's header
		/// </returns>
		/// <exception cref="Exception">if instance doesn't have access to any
		/// dataset
		/// </exception>
		//@ requires m_Dataset != null;
		public virtual bool equalHeaders(Instance inst)
		{
			
			if (m_Dataset == null)
			{
				throw new Exception("Instance doesn't have access to a dataset!");
			}
			return m_Dataset.equalHeaders(inst.m_Dataset);
		}
		
		/// <summary> Tests whether an instance has a missing value. Skips the class attribute if set.</summary>
		/// <returns> true if instance has a missing value.
		/// </returns>
		/// <exception cref="Exception">if instance doesn't have access to any
		/// dataset
		/// </exception>
		//@ requires m_Dataset != null;
		public virtual bool hasMissingValue()
		{
			
			if (m_Dataset == null)
			{
				throw new Exception("Instance doesn't have access to a dataset!");
			}
			for (int i = 0; i < numAttributes(); i++)
			{
				if (i != classIndex())
				{
					if (isMissing(i))
					{
						return true;
					}
				}
			}
			return false;
		}
		
		/// <summary> Returns the index of the attribute stored at the given position.
		/// Just returns the given value.
		/// 
		/// </summary>
		/// <param name="position">the position 
		/// </param>
		/// <returns> the index of the attribute stored at the given position
		/// </returns>
		public virtual int index(int position)
		{
			
			return position;
		}
		
		/// <summary> Inserts an attribute at the given position (0 to 
		/// numAttributes()). Only succeeds if the instance does not
		/// have access to any dataset because otherwise inconsistencies
		/// could be introduced.
		/// 
		/// </summary>
		/// <param name="pos">the attribute's position
		/// </param>
		/// <exception cref="RuntimeException">if the instance has accesss to a
		/// dataset
		/// </exception>
		/// <exception cref="IllegalArgumentException">if the position is out of range
		/// </exception>
		//@ requires m_Dataset == null;
		//@ requires 0 <= position && position <= numAttributes();
		public virtual void  insertAttributeAt(int position)
		{
			
			if (m_Dataset != null)
			{
				throw new System.SystemException("Instance has accesss to a dataset!");
			}
			if ((position < 0) || (position > numAttributes()))
			{
				throw new System.ArgumentException("Can't insert attribute: index out " + "of range");
			}
			forceInsertAttributeAt(position);
		}
		
		/// <summary> Tests if a specific value is "missing".
		/// 
		/// </summary>
		/// <param name="attIndex">the attribute's index
		/// </param>
		public virtual bool isMissing(int attIndex)
		{
			
			if (System.Double.IsNaN(m_AttValues[attIndex]))
			{
				return true;
			}
			return false;
		}
		
		/// <summary> Tests if a specific value is "missing". Does
		/// the same thing as isMissing() if applied to an Instance.
		/// 
		/// </summary>
		/// <param name="indexOfIndex">the index of the attribute's index 
		/// </param>
		public virtual bool isMissingSparse(int indexOfIndex)
		{
			
			if (System.Double.IsNaN(m_AttValues[indexOfIndex]))
			{
				return true;
			}
			return false;
		}
		
		/// <summary> Tests if a specific value is "missing".
		/// The given attribute has to belong to a dataset.
		/// 
		/// </summary>
		/// <param name="att">the attribute
		/// </param>
		public virtual bool isMissing(Attribute att)
		{
			
			return isMissing(att.index());
		}
		
		/// <summary> Tests if the given value codes "missing".
		/// 
		/// </summary>
		/// <param name="val">the value to be tested
		/// </param>
		/// <returns> true if val codes "missing"
		/// </returns>
		public static bool isMissingValue(double val)
		{
			
			return System.Double.IsNaN(val);
		}
		
		/// <summary> Merges this instance with the given instance and returns
		/// the result. Dataset is set to null.
		/// 
		/// </summary>
		/// <param name="inst">the instance to be merged with this one
		/// </param>
		/// <returns> the merged instances
		/// </returns>
		public virtual Instance mergeInstance(Instance inst)
		{
			
			int m = 0;
			double[] newVals = new double[numAttributes() + inst.numAttributes()];
			for (int j = 0; j < numAttributes(); j++, m++)
			{
				newVals[m] = value_Renamed(j);
			}
			for (int j = 0; j < inst.numAttributes(); j++, m++)
			{
				newVals[m] = inst.value_Renamed(j);
			}
			return new Instance(1.0, newVals);
		}
		
		/// <summary> Returns the double that codes "missing".
		/// 
		/// </summary>
		/// <returns> the double that codes "missing"
		/// </returns>
		public static double missingValue()
		{
			
			return MISSING_VALUE;
		}
		
		/// <summary> Returns the number of attributes.
		/// 
		/// </summary>
		/// <returns> the number of attributes as an integer
		/// </returns>
		//@ ensures \result == m_AttValues.length;
		public virtual int numAttributes()
		{
			
			return m_AttValues.Length;
		}
		
		/// <summary> Returns the number of class labels.
		/// 
		/// </summary>
		/// <returns> the number of class labels as an integer if the 
		/// class attribute is nominal, 1 otherwise.
		/// </returns>
		/// <exception cref="Exception">if instance doesn't have access to any
		/// dataset
		/// </exception>
		//@ requires m_Dataset != null;
		public virtual int numClasses()
		{
			
			if (m_Dataset == null)
			{
				throw new Exception("Instance doesn't have access to a dataset!");
			}
			return m_Dataset.numClasses();
		}
		
		/// <summary> Returns the number of values present. Always the same as numAttributes().
		/// 
		/// </summary>
		/// <returns> the number of values
		/// </returns>
		//@ ensures \result == m_AttValues.length;
		public virtual int numValues()
		{
			
			return m_AttValues.Length;
		}
		
		/// <summary> Replaces all missing values in the instance with the
		/// values contained in the given array. A deep copy of
		/// the vector of attribute values is performed before the
		/// values are replaced.
		/// 
		/// </summary>
		/// <param name="array">containing the means and modes
		/// </param>
		/// <exception cref="IllegalArgumentException">if numbers of attributes are unequal
		/// </exception>
		public virtual void  replaceMissingValues(double[] array)
		{
			
			if ((array == null) || (array.Length != m_AttValues.Length))
			{
				throw new System.ArgumentException("Unequal number of attributes!");
			}
			freshAttributeVector();
			for (int i = 0; i < m_AttValues.Length; i++)
			{
				if (isMissing(i))
				{
					m_AttValues[i] = array[i];
				}
			}
		}
		
		/// <summary> Sets the class value of an instance to be "missing". A deep copy of
		/// the vector of attribute values is performed before the
		/// value is set to be missing.
		/// 
		/// </summary>
		/// <exception cref="Exception">if the class is not set
		/// </exception>
		/// <exception cref="Exception">if the instance doesn't
		/// have access to a dataset
		/// </exception>
		//@ requires classIndex() >= 0;
		public virtual void  setClassMissing()
		{
			
			if (classIndex() < 0)
			{
				throw new Exception("Class is not set!");
			}
			setMissing(classIndex());
		}
		
		/// <summary> Sets the class value of an instance to the given value (internal
		/// floating-point format).  A deep copy of the vector of attribute
		/// values is performed before the value is set.
		/// 
		/// </summary>
		/// <param name="value">the new attribute value (If the corresponding
		/// attribute is nominal (or a string) then this is the new value's
		/// index as a double).  
		/// </param>
		/// <exception cref="Exception">if the class is not set
		/// </exception>
		/// <exception cref="UnaddignedDatasetException">if the instance doesn't
		/// have access to a dataset 
		/// </exception>
		//@ requires classIndex() >= 0;
		public virtual void  setClassValue(double value_Renamed)
		{
			
			if (classIndex() < 0)
			{
				throw new Exception("Class is not set!");
			}
			setValue(classIndex(), value_Renamed);
		}
		
		/// <summary> Sets the class value of an instance to the given value. A deep
		/// copy of the vector of attribute values is performed before the
		/// value is set.
		/// 
		/// </summary>
		/// <param name="value">the new class value (If the class
		/// is a string attribute and the value can't be found,
		/// the value is added to the attribute).
		/// </param>
		/// <exception cref="Exception">if the class is not set
		/// </exception>
		/// <exception cref="Exception">if the dataset is not set
		/// </exception>
		/// <exception cref="IllegalArgumentException">if the attribute is not
		/// nominal or a string, or the value couldn't be found for a nominal
		/// attribute 
		/// </exception>
		//@ requires classIndex() >= 0;
		public void  setClassValue(System.String value_Renamed)
		{
			
			if (classIndex() < 0)
			{
				throw new Exception("Class is not set!");
			}
			setValue(classIndex(), value_Renamed);
		}
		
		/// <summary> Sets a specific value to be "missing". Performs a deep copy
		/// of the vector of attribute values before the value is set to
		/// be missing.
		/// 
		/// </summary>
		/// <param name="attIndex">the attribute's index
		/// </param>
		public void  setMissing(int attIndex)
		{
			
			setValue(attIndex, MISSING_VALUE);
		}
		
		/// <summary> Sets a specific value to be "missing". Performs a deep copy
		/// of the vector of attribute values before the value is set to
		/// be missing. The given attribute has to belong to a dataset.
		/// 
		/// </summary>
		/// <param name="att">the attribute
		/// </param>
		public void  setMissing(Attribute att)
		{
			
			setMissing(att.index());
		}
		
		/// <summary> Sets a specific value in the instance to the given value 
		/// (internal floating-point format). Performs a deep copy
		/// of the vector of attribute values before the value is set.
		/// 
		/// </summary>
		/// <param name="attIndex">the attribute's index 
		/// </param>
		/// <param name="value">the new attribute value (If the corresponding
		/// attribute is nominal (or a string) then this is the new value's
		/// index as a double).  
		/// </param>
		public virtual void  setValue(int attIndex, double value_Renamed)
		{
			
			freshAttributeVector();
			m_AttValues[attIndex] = value_Renamed;
		}
		
		/// <summary> Sets a specific value in the instance to the given value 
		/// (internal floating-point format). Performs a deep copy
		/// of the vector of attribute values before the value is set.
		/// Does exactly the same thing as setValue().
		/// 
		/// </summary>
		/// <param name="indexOfIndex">the index of the attribute's index 
		/// </param>
		/// <param name="value">the new attribute value (If the corresponding
		/// attribute is nominal (or a string) then this is the new value's
		/// index as a double).  
		/// </param>
		public virtual void  setValueSparse(int indexOfIndex, double value_Renamed)
		{
			
			freshAttributeVector();
			m_AttValues[indexOfIndex] = value_Renamed;
		}
		
		/// <summary> Sets a value of a nominal or string attribute to the given
		/// value. Performs a deep copy of the vector of attribute values
		/// before the value is set.
		/// 
		/// </summary>
		/// <param name="attIndex">the attribute's index
		/// </param>
		/// <param name="value">the new attribute value (If the attribute
		/// is a string attribute and the value can't be found,
		/// the value is added to the attribute).
		/// </param>
		/// <exception cref="Exception">if the dataset is not set
		/// </exception>
		/// <exception cref="IllegalArgumentException">if the selected
		/// attribute is not nominal or a string, or the supplied value couldn't 
		/// be found for a nominal attribute 
		/// </exception>
		//@ requires m_Dataset != null;
		public void  setValue(int attIndex, System.String value_Renamed)
		{
			
			int valIndex;
			
			if (m_Dataset == null)
			{
				throw new Exception("Instance doesn't have access to a dataset!");
			}
			if (!attribute(attIndex).Nominal && !attribute(attIndex).String)
			{
				throw new System.ArgumentException("Attribute neither nominal nor string!");
			}
			valIndex = attribute(attIndex).indexOfValue(value_Renamed);
			if (valIndex == - 1)
			{
				if (attribute(attIndex).Nominal)
				{
					throw new System.ArgumentException("Value not defined for given nominal attribute!");
				}
				else
				{
					attribute(attIndex).forceAddValue(value_Renamed);
					valIndex = attribute(attIndex).indexOfValue(value_Renamed);
				}
			}
			setValue(attIndex, (double) valIndex);
		}
		
		/// <summary> Sets a specific value in the instance to the given value
		/// (internal floating-point format). Performs a deep copy of the
		/// vector of attribute values before the value is set, so if you are
		/// planning on calling setValue many times it may be faster to
		/// create a new instance using toDoubleArray.  The given attribute
		/// has to belong to a dataset.
		/// 
		/// </summary>
		/// <param name="att">the attribute 
		/// </param>
		/// <param name="value">the new attribute value (If the corresponding
		/// attribute is nominal (or a string) then this is the new value's
		/// index as a double).  
		/// </param>
		public void  setValue(Attribute att, double value_Renamed)
		{
			
			setValue(att.index(), value_Renamed);
		}
		
		/// <summary> Sets a value of an nominal or string attribute to the given
		/// value. Performs a deep copy of the vector of attribute values
		/// before the value is set, so if you are planning on calling setValue many
		/// times it may be faster to create a new instance using toDoubleArray.
		/// The given attribute has to belong to a dataset.
		/// 
		/// </summary>
		/// <param name="att">the attribute
		/// </param>
		/// <param name="value">the new attribute value (If the attribute
		/// is a string attribute and the value can't be found,
		/// the value is added to the attribute).
		/// </param>
		/// <exception cref="IllegalArgumentException">if the the attribute is not
		/// nominal or a string, or the value couldn't be found for a nominal
		/// attribute 
		/// </exception>
		public void  setValue(Attribute att, System.String value_Renamed)
		{
			
			if (!att.Nominal && !att.String)
			{
				throw new System.ArgumentException("Attribute neither nominal nor string!");
			}
			int valIndex = att.indexOfValue(value_Renamed);
			if (valIndex == - 1)
			{
				if (att.Nominal)
				{
					throw new System.ArgumentException("Value not defined for given nominal attribute!");
				}
				else
				{
					att.forceAddValue(value_Renamed);
					valIndex = att.indexOfValue(value_Renamed);
				}
			}
			setValue(att.index(), (double) valIndex);
		}
		
		/// <summary> Returns the string value of a nominal, string, or date attribute
		/// for the instance.
		/// 
		/// </summary>
		/// <param name="attIndex">the attribute's index
		/// </param>
		/// <returns> the value as a string
		/// </returns>
		/// <exception cref="IllegalArgumentException">if the attribute is not a nominal,
		/// string, or date attribute.
		/// </exception>
		/// <exception cref="Exception">if the instance doesn't belong
		/// to a dataset.
		/// </exception>
		//@ requires m_Dataset != null;
		public System.String stringValue(int attIndex)
		{
			
			if (m_Dataset == null)
			{
				throw new Exception("Instance doesn't have access to a dataset!");
			}
			return stringValue(m_Dataset.attribute(attIndex));
		}
		
		/// <summary> Returns the string value of a nominal, string, or date attribute
		/// for the instance.
		/// 
		/// </summary>
		/// <param name="att">the attribute
		/// </param>
		/// <returns> the value as a string
		/// </returns>
		/// <exception cref="IllegalArgumentException">if the attribute is not a nominal,
		/// string, or date attribute.
		/// </exception>
		/// <exception cref="Exception">if the instance doesn't belong
		/// to a dataset.
		/// </exception>
		public System.String stringValue(Attribute att)
		{
			
			int attIndex = att.index();
			switch (att.type())
			{
				
				case Attribute.NOMINAL: 
				case Attribute.STRING: 
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					return att.value_Renamed((int) value_Renamed(attIndex));
				
				case Attribute.DATE: 
					return att.formatDate(value_Renamed(attIndex));
				
				default: 
					throw new System.ArgumentException("Attribute isn't nominal, string or date!");
				
			}
		}
		
		/// <summary> Returns the values of each attribute as an array of doubles.
		/// 
		/// </summary>
		/// <returns> an array containing all the instance attribute values
		/// </returns>
		public virtual double[] toDoubleArray()
		{
			
			double[] newValues = new double[m_AttValues.Length];
			Array.Copy(m_AttValues, 0, newValues, 0, m_AttValues.Length);
			return newValues;
		}
		
		/// <summary> Returns the description of one instance. If the instance
		/// doesn't have access to a dataset, it returns the internal
		/// floating-point values. Quotes string
		/// values that contain whitespace characters.
		/// 
		/// </summary>
		/// <returns> the instance's description as a string
		/// </returns>
		public override System.String ToString()
		{
			
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			
			for (int i = 0; i < m_AttValues.Length; i++)
			{
				if (i > 0)
					text.Append(",");
				text.Append(toString(i));
			}
			
			return text.ToString();
		}
		
		/// <summary> Returns the description of one value of the instance as a 
		/// string. If the instance doesn't have access to a dataset, it 
		/// returns the internal floating-point value. Quotes string
		/// values that contain whitespace characters, or if they
		/// are a question mark.
		/// 
		/// </summary>
		/// <param name="attIndex">the attribute's index
		/// </param>
		/// <returns> the value's description as a string
		/// </returns>
		public System.String toString(int attIndex)
		{
			
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			
			if (isMissing(attIndex))
			{
				text.Append("?");
			}
			else
			{
				if (m_Dataset == null)
				{
					text.Append(Utils.doubleToString(m_AttValues[attIndex], 6));
				}
				else
				{
					switch (m_Dataset.attribute(attIndex).type())
					{
						
						case Attribute.NOMINAL: 
						case Attribute.STRING: 
						case Attribute.DATE: 
							text.Append(Utils.quote(stringValue(attIndex)));
							break;
						
						case Attribute.NUMERIC: 
							text.Append(Utils.doubleToString(value_Renamed(attIndex), 6));
							break;
						
						default: 
							throw new System.SystemException("Unknown attribute type");
						
					}
				}
			}
			return text.ToString();
		}
		
		/// <summary> Returns the description of one value of the instance as a 
		/// string. If the instance doesn't have access to a dataset it 
		/// returns the internal floating-point value. Quotes string
		/// values that contain whitespace characters, or if they
		/// are a question mark.
		/// The given attribute has to belong to a dataset.
		/// 
		/// </summary>
		/// <param name="att">the attribute
		/// </param>
		/// <returns> the value's description as a string
		/// </returns>
		public System.String toString(Attribute att)
		{
			
			return toString(att.index());
		}
		
		/// <summary> Returns an instance's attribute value in internal format.
		/// 
		/// </summary>
		/// <param name="attIndex">the attribute's index
		/// </param>
		/// <returns> the specified value as a double (If the corresponding
		/// attribute is nominal (or a string) then it returns the value's index as a 
		/// double).
		/// </returns>
		public virtual double value_Renamed(int attIndex)
		{
			
			return m_AttValues[attIndex];
		}
		
		/// <summary> Returns an instance's attribute value in internal format.
		/// Does exactly the same thing as value() if applied to an Instance.
		/// 
		/// </summary>
		/// <param name="indexOfIndex">the index of the attribute's index
		/// </param>
		/// <returns> the specified value as a double (If the corresponding
		/// attribute is nominal (or a string) then it returns the value's index as a 
		/// double).
		/// </returns>
		public virtual double valueSparse(int indexOfIndex)
		{
			
			return m_AttValues[indexOfIndex];
		}
		
		/// <summary> Returns an instance's attribute value in internal format.
		/// The given attribute has to belong to a dataset.
		/// 
		/// </summary>
		/// <param name="att">the attribute
		/// </param>
		/// <returns> the specified value as a double (If the corresponding
		/// attribute is nominal (or a string) then it returns the value's index as a
		/// double).
		/// </returns>
		public virtual double value_Renamed(Attribute att)
		{
			
			return value_Renamed(att.index());
		}
		
		/// <summary> Returns the instance's weight.
		/// 
		/// </summary>
		/// <returns> the instance's weight as a double
		/// </returns>
		public double weight()
		{
			
			return m_Weight;
		}
		
		/// <summary> Deletes an attribute at the given position (0 to 
		/// numAttributes() - 1).
		/// 
		/// </summary>
		/// <param name="pos">the attribute's position
		/// </param>
		
		internal virtual void  forceDeleteAttributeAt(int position)
		{
			
			double[] newValues = new double[m_AttValues.Length - 1];
			
			Array.Copy(m_AttValues, 0, newValues, 0, position);
			if (position < m_AttValues.Length - 1)
			{
				Array.Copy(m_AttValues, position + 1, newValues, position, m_AttValues.Length - (position + 1));
			}
			m_AttValues = newValues;
		}
		
		/// <summary> Inserts an attribute at the given position
		/// (0 to numAttributes()) and sets its value to be missing. 
		/// 
		/// </summary>
		/// <param name="pos">the attribute's position
		/// </param>
		internal virtual void  forceInsertAttributeAt(int position)
		{
			
			double[] newValues = new double[m_AttValues.Length + 1];
			
			Array.Copy(m_AttValues, 0, newValues, 0, position);
			newValues[position] = MISSING_VALUE;
			Array.Copy(m_AttValues, position, newValues, position + 1, m_AttValues.Length - position);
			m_AttValues = newValues;
		}
		
		/// <summary> Private constructor for subclasses. Does nothing.</summary>
		protected internal Instance()
		{
		}
		
		/// <summary> Clones the attribute vector of the instance and
		/// overwrites it with the clone.
		/// </summary>
		private void  freshAttributeVector()
		{
			
			m_AttValues = toDoubleArray();
		}
		
		/// <summary> Main method for testing this class.</summary>
		//@ requires options != null;
		//	public static void main(String[] options) 
		//	{
		//		try 
		//		{
		//
		//			// Create numeric attributes "length" and "weight"
		//			Attribute length = new Attribute("length");
		//			Attribute weight = new Attribute("weight");
		//      
		//			// Create vector to hold nominal values "first", "second", "third" 
		//			FastVector my_nominal_values = new FastVector(3); 
		//			my_nominal_values.addElement("first"); 
		//			my_nominal_values.addElement("second"); 
		//			my_nominal_values.addElement("third"); 
		//      
		//			// Create nominal attribute "position" 
		//			Attribute position = new Attribute("position", my_nominal_values);
		//      
		//			// Create vector of the above attributes 
		//			FastVector attributes = new FastVector(3);
		//			attributes.addElement(length);
		//			attributes.addElement(weight);
		//			attributes.addElement(position);
		//      
		//			// Create the empty dataset "race" with above attributes
		//			Instances race = new Instances("race", attributes, 0);
		//      
		//			// Make position the class attribute
		//			race.setClassIndex(position.index());
		//      
		//			// Create empty instance with three attribute values
		//			Instance inst = new Instance(3);
		//      
		//			// Set instance's values for the attributes "length", "weight", and "position"
		//			inst.setValue(length, 5.3);
		//			inst.setValue(weight, 300);
		//			inst.setValue(position, "first");
		//      
		//			// Set instance's dataset to be the dataset "race"
		//			inst.setDataset(race);
		//      
		//			// Print the instance
		//			System.out.println("The instance: " + inst);
		//      
		//			// Print the first attribute
		//			System.out.println("First attribute: " + inst.attribute(0));
		//      
		//			// Print the class attribute
		//			System.out.println("Class attribute: " + inst.classAttribute());
		//      
		//			// Print the class index
		//			System.out.println("Class index: " + inst.classIndex());
		//      
		//			// Say if class is missing
		//			System.out.println("Class is missing: " + inst.classIsMissing());
		//      
		//			// Print the instance's class value in internal format
		//			System.out.println("Class value (internal format): " + inst.classValue());
		//      
		//			// Print a shallow copy of this instance
		//			Instance copy = (Instance) inst.copy();
		//			System.out.println("Shallow copy: " + copy);
		//      
		//			// Set dataset for shallow copy
		//			copy.setDataset(inst.dataset());
		//			System.out.println("Shallow copy with dataset set: " + copy);
		//      
		//			// Unset dataset for copy, delete first attribute, and insert it again
		//			copy.setDataset(null);
		//			copy.deleteAttributeAt(0);
		//			copy.insertAttributeAt(0);
		//			copy.setDataset(inst.dataset());
		//			System.out.println("Copy with first attribute deleted and inserted: " + copy); 
		//      
		//			// Enumerate attributes (leaving out the class attribute)
		//			System.out.println("Enumerating attributes (leaving out class):");
		//			Enumeration enu = inst.enumerateAttributes();
		//			while (enu.hasMoreElements()) 
		//			{
		//				Attribute att = (Attribute) enu.nextElement();
		//				System.out.println(att);
		//			}
		//      
		//			// Headers are equivalent?
		//			System.out.println("Header of original and copy equivalent: " +
		//				inst.equalHeaders(copy));
		//
		//			// Test for missing values
		//			System.out.println("Length of copy missing: " + copy.isMissing(length));
		//			System.out.println("Weight of copy missing: " + copy.isMissing(weight.index()));
		//			System.out.println("Length of copy missing: " + 
		//				Instance.isMissingValue(copy.value(length)));
		//			System.out.println("Missing value coded as: " + Instance.missingValue());
		//
		//			// Prints number of attributes and classes
		//			System.out.println("Number of attributes: " + copy.numAttributes());
		//			System.out.println("Number of classes: " + copy.numClasses());
		//
		//			// Replace missing values
		//			double[] meansAndModes = {2, 3, 0};
		//			copy.replaceMissingValues(meansAndModes);
		//			System.out.println("Copy with missing value replaced: " + copy);
		//
		//			// Setting and getting values and weights
		//			copy.setClassMissing();
		//			System.out.println("Copy with missing class: " + copy);
		//			copy.setClassValue(0);
		//			System.out.println("Copy with class value set to first value: " + copy);
		//			copy.setClassValue("third");
		//			System.out.println("Copy with class value set to \"third\": " + copy);
		//			copy.setMissing(1);
		//			System.out.println("Copy with second attribute set to be missing: " + copy);
		//			copy.setMissing(length);
		//			System.out.println("Copy with length set to be missing: " + copy);
		//			copy.setValue(0, 0);
		//			System.out.println("Copy with first attribute set to 0: " + copy);
		//			copy.setValue(weight, 1);
		//			System.out.println("Copy with weight attribute set to 1: " + copy);
		//			copy.setValue(position, "second");
		//			System.out.println("Copy with position set to \"second\": " + copy);
		//			copy.setValue(2, "first");
		//			System.out.println("Copy with last attribute set to \"first\": " + copy);
		//			System.out.println("Current weight of instance copy: " + copy.weight());
		//			copy.setWeight(2);
		//			System.out.println("Current weight of instance copy (set to 2): " + copy.weight());
		//			System.out.println("Last value of copy: " + copy.toString(2));
		//			System.out.println("Value of position for copy: " + copy.toString(position));
		//			System.out.println("Last value of copy (internal format): " + copy.value(2));
		//			System.out.println("Value of position for copy (internal format): " + 
		//				copy.value(position));
		//		} 
		//		catch (Exception e) 
		//		{
		//			e.printStackTrace();
		//		}
		//	}
	}
}