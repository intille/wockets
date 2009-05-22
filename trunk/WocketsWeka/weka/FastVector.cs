/*
*    FastVector.java
*    Copyright (C) 1999 Eibe Frank
*/
using System;
namespace weka.core
{
	
	/// <summary> Implements a fast vector class without synchronized
	/// methods. Replaces java.util.Vector. (Synchronized methods tend to
	/// be slow.)
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.11 $ 
	/// </version>
#if !PocketPC
    [Serializable]
#endif
	public class FastVector : Copyable
	{
		/// <summary> Sets the vector's capacity to the given value.
		/// 
		/// </summary>
		/// <param name="capacity">the new capacity
		/// </param>
		virtual public int Capacity
		{
			set
			{
				
				System.Object[] newObjects = new System.Object[value];
				
				Array.Copy(m_Objects, 0, newObjects, 0, System.Math.Min(value, m_Size));
				m_Objects = newObjects;
				if (m_Objects.Length < m_Size)
					m_Size = m_Objects.Length;
			}
			
		}
		
		
		/// <summary>The array of objects. </summary>
		private System.Object[] m_Objects;
		//@ invariant m_Objects != null;
		//@ invariant m_Objects.length >= 0;
		
		/// <summary>The current size; </summary>
		private int m_Size = 0;
		//@ invariant 0 <= m_Size;
		//@ invariant m_Size <= m_Objects.length;
		
		/// <summary>The capacity increment </summary>
		private int m_CapacityIncrement = 1;
		//@ invariant 1 <= m_CapacityIncrement;
		
		/// <summary>The capacity multiplier. </summary>
		private int m_CapacityMultiplier = 2;
		//@ invariant 1 <= m_CapacityMultiplier;
		
		// Make sure the size will increase...
		//@ invariant 3 <= m_CapacityMultiplier + m_CapacityIncrement;
		
		/// <summary> Constructs an empty vector with initial
		/// capacity zero.
		/// </summary>
		public FastVector()
		{
			
			m_Objects = new System.Object[0];
		}
		
		/// <summary> Constructs a vector with the given capacity.
		/// 
		/// </summary>
		/// <param name="capacity">the vector's initial capacity
		/// </param>
		//@ requires capacity >= 0;
		public FastVector(int capacity)
		{
			
			m_Objects = new System.Object[capacity];
		}
		
		/// <summary> Adds an element to this vector. Increases its
		/// capacity if its not large enough.
		/// 
		/// </summary>
		/// <param name="element">the element to add
		/// </param>
		public void  addElement(System.Object element)
		{
			
			System.Object[] newObjects;
			
			if (m_Size == m_Objects.Length)
			{
				newObjects = new System.Object[m_CapacityMultiplier * (m_Objects.Length + m_CapacityIncrement)];
				Array.Copy(m_Objects, 0, newObjects, 0, m_Size);
				m_Objects = newObjects;
			}
			m_Objects[m_Size] = element;
			m_Size++;
		}
		
		/// <summary> Returns the capacity of the vector.
		/// 
		/// </summary>
		/// <returns> the capacity of the vector
		/// </returns>
		//@ ensures \result == m_Objects.length;
		public int capacity()
		{
			
			return m_Objects.Length;
		}
		
		/// <summary> Produces a shallow copy of this vector.
		/// 
		/// </summary>
		/// <returns> the new vector
		/// </returns>
		public System.Object copy()
		{
			
			FastVector copy = new FastVector(m_Objects.Length);
			
			copy.m_Size = m_Size;
			copy.m_CapacityIncrement = m_CapacityIncrement;
			copy.m_CapacityMultiplier = m_CapacityMultiplier;
			Array.Copy(m_Objects, 0, copy.m_Objects, 0, m_Size);
			return copy;
		}
		
		/// <summary> Clones the vector and shallow copies all its elements.
		/// The elements have to implement the Copyable interface.
		/// 
		/// </summary>
		/// <returns> the new vector
		/// </returns>
		public System.Object copyXmlElements()
		{
			
			FastVector copy = new FastVector(m_Objects.Length);
			
			copy.m_Size = m_Size;
			copy.m_CapacityIncrement = m_CapacityIncrement;
			copy.m_CapacityMultiplier = m_CapacityMultiplier;
			for (int i = 0; i < m_Size; i++)
			{
				copy.m_Objects[i] = ((Copyable) m_Objects[i]).copy();
			}
			return copy;
		}
		
		/// <summary> Returns the element at the given position.
		/// 
		/// </summary>
		/// <param name="index">the element's index
		/// </param>
		/// <returns> the element with the given index
		/// </returns>
		//@ requires 0 <= index;
		//@ requires index < m_Objects.length;
		public System.Object elementAt(int index)
		{
			
			return m_Objects[index];
		}
		
		/// <summary> Returns an enumeration of this vector.
		/// 
		/// </summary>
		/// <returns> an enumeration of this vector
		/// </returns>
		public System.Collections.IEnumerator elements()
		{
			
			return new FastVectorEnumeration(this);
		}
		
		/// <summary> Returns an enumeration of this vector, skipping the
		/// element with the given index.
		/// 
		/// </summary>
		/// <param name="index">the element to skip
		/// </param>
		/// <returns> an enumeration of this vector
		/// </returns>
		//@ requires 0 <= index && index < size();
		public System.Collections.IEnumerator elements(int index)
		{
			
			return new FastVectorEnumeration(this, index);
		}
		
		/// <summary> added by akibriya</summary>
		public virtual bool contains(System.Object o)
		{
			if (o == null)
				return false;
			
			for (int i = 0; i < m_Objects.Length; i++)
				if (o.Equals(m_Objects[i]))
					return true;
			
			return false;
		}
		
		
		/// <summary> Returns the first element of the vector.
		/// 
		/// </summary>
		/// <returns> the first element of the vector
		/// </returns>
		//@ requires m_Size > 0;
		public System.Object firstXmlElement()
		{
			
			return m_Objects[0];
		}
		
		/// <summary> Searches for the first occurence of the given argument, 
		/// testing for equality using the equals method. 
		/// 
		/// </summary>
		/// <param name="element">the element to be found
		/// </param>
		/// <returns> the index of the first occurrence of the argument 
		/// in this vector; returns -1 if the object is not found
		/// </returns>
		public int indexOf(System.Object element)
		{
			
			for (int i = 0; i < m_Size; i++)
			{
				if (element.Equals(m_Objects[i]))
				{
					return i;
				}
			}
			return - 1;
		}
		
		/// <summary> Inserts an element at the given position.
		/// 
		/// </summary>
		/// <param name="element">the element to be inserted
		/// </param>
		/// <param name="index">the element's index
		/// </param>
		public void  insertElementAt(System.Object element, int index)
		{
			
			System.Object[] newObjects;
			
			if (m_Size < m_Objects.Length)
			{
				Array.Copy(m_Objects, index, m_Objects, index + 1, m_Size - index);
				m_Objects[index] = element;
			}
			else
			{
				newObjects = new System.Object[m_CapacityMultiplier * (m_Objects.Length + m_CapacityIncrement)];
				Array.Copy(m_Objects, 0, newObjects, 0, index);
				newObjects[index] = element;
				Array.Copy(m_Objects, index, newObjects, index + 1, m_Size - index);
				m_Objects = newObjects;
			}
			m_Size++;
		}
		
		/// <summary> Returns the last element of the vector.
		/// 
		/// </summary>
		/// <returns> the last element of the vector
		/// </returns>
		//@ requires m_Size > 0;
		public System.Object lastElement()
		{
			
			return m_Objects[m_Size - 1];
		}
		
		/// <summary> Deletes an element from this vector.
		/// 
		/// </summary>
		/// <param name="index">the index of the element to be deleted
		/// </param>
		//@ requires 0 <= index && index < m_Size;
		public void  removeElementAt(int index)
		{
			
			Array.Copy(m_Objects, index + 1, m_Objects, index, m_Size - index - 1);
			m_Size--;
		}
		
		/// <summary> Removes all components from this vector and sets its 
		/// size to zero. 
		/// </summary>
		public void  removeAllElements()
		{
			
			m_Objects = new System.Object[m_Objects.Length];
			m_Size = 0;
		}
		
		/// <summary> Appends all elements of the supplied vector to this vector.
		/// 
		/// </summary>
		/// <param name="toAppend">the FastVector containing elements to append.
		/// </param>
		public void  appendXmlElements(FastVector toAppend)
		{
			
			Capacity = size() + toAppend.size();
			Array.Copy(toAppend.m_Objects, 0, m_Objects, size(), toAppend.size());
			m_Size = m_Objects.Length;
		}
		
		/// <summary> Returns all the elements of this vector as an array
		/// 
		/// </summary>
		/// <param name="an">array containing all the elements of this vector
		/// </param>
		public System.Object[] toArray()
		{
			
			System.Object[] newObjects = new System.Object[size()];
			Array.Copy(m_Objects, 0, newObjects, 0, size());
			return newObjects;
		}
		
		/// <summary> Sets the element at the given index.
		/// 
		/// </summary>
		/// <param name="element">the element to be put into the vector
		/// </param>
		/// <param name="index">the index at which the element is to be placed
		/// </param>
		//@ requires 0 <= index && index < size();
		public void  setXmlElementAt(System.Object element, int index)
		{
			
			m_Objects[index] = element;
		}
		
		/// <summary> Returns the vector's current size.
		/// 
		/// </summary>
		/// <returns> the vector's current size
		/// </returns>
		//@ ensures \result == m_Size;
		public int size()
		{
			
			return m_Size;
		}
		
		/// <summary> Swaps two elements in the vector.
		/// 
		/// </summary>
		/// <param name="first">index of the first element
		/// </param>
		/// <param name="second">index of the second element
		/// </param>
		//@ requires 0 <= first && first < size();
		//@ requires 0 <= second && second < size();
		public void  swap(int first, int second)
		{
			
			System.Object help = m_Objects[first];
			
			m_Objects[first] = m_Objects[second];
			m_Objects[second] = help;
		}
		
		/// <summary> Sets the vector's capacity to its size.</summary>
		public void  trimToSize()
		{
			
			System.Object[] newObjects = new System.Object[m_Size];
			
			Array.Copy(m_Objects, 0, newObjects, 0, m_Size);
			m_Objects = newObjects;
		}
	}
}