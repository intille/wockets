/*
*    Queue.java
*    Copyright (C) 1999 Len Trigg
*
*    Modified March-May 2004 by Mark Utting to add JML specs
*    (this was done as the example solution of an assignment for a
*     software engineering course, so the specifications are more precise
*     and complete than one would normally do).
*    Passed a static analysis using ESC/Java-2.0a6 with no warnings.*/
using System;
namespace weka.core
{
	
	/// <summary> Class representing a FIFO queue.
	/// 
	/// </summary>
	/// <author>  Len Trigg (trigg@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.7 $
	/// </version>
#if !PocketPC
    [Serializable]
#endif
	public class Queue:System.Object
	{
		
		//UPGRADE_NOTE: Field 'EnclosingInstance' was added to class 'QueueXmlNode' to access its enclosing instance. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1019'"
		/// <summary> Represents one node in the queue.</summary>
#if !PocketPC
        [Serializable]
#endif
		protected internal class QueueXmlNode
		{
			private void  InitBlock(Queue enclosingInstance)
			{
				this.enclosingInstance = enclosingInstance;
			}
			private Queue enclosingInstance;
			public Queue Enclosing_Instance
			{
				get
				{
					return enclosingInstance;
				}
				
			}
			
			/// <summary>The next node in the queue </summary>
			protected internal QueueXmlNode m_Next;
			
			/// <summary>The nodes contents</summary>
			protected internal System.Object m_Contents;
			
			/// <summary> Creates a queue node with the given contents </summary>
			//@ requires contents != null;
			//@ assignable m_Contents, m_Next;
			//@ ensures m_Contents == contents;
			//@ ensures m_Next == null;
			public QueueXmlNode(Queue enclosingInstance, System.Object contents)
			{
				InitBlock(enclosingInstance);
				m_Contents = contents;
				next(null);
			}
			
			/// <summary> Sets the next node in the queue, and returns it.</summary>
			//@ requires next != this ;
			//@ assignable m_Next;
			//@ ensures m_Next==next && \result==next;
			public virtual QueueXmlNode next(QueueXmlNode next)
			{
				return m_Next = next;
			} //@ nowarn Invariant; // Because it stupidly checks the Queue invariant!
			
			/// <summary> Gets the next node in the queue. </summary>
			//@ ensures \result == m_Next;
			public virtual QueueXmlNode next()
			{
				return m_Next;
			}
			
			/// <summary> Sets the contents of the node.</summary>
			//@ requires contents != null;
			//@ assignable m_Contents;
			//@ ensures  m_Contents == contents && \result == contents;
			public virtual System.Object contents(System.Object contents)
			{
				return m_Contents = contents;
			}
			
			/// <summary> Returns the contents in the node.</summary>
			//@ ensures \result == m_Contents;
			public virtual System.Object contents()
			{
				return m_Contents;
			}
		}
		
		/// <summary>Store a reference to the head of the queue </summary>
		protected internal QueueXmlNode m_Head = null;
		
		/// <summary>Store a reference to the tail of the queue </summary>
		protected internal QueueXmlNode m_Tail = null;
		
		/// <summary>Store the c m_Tail.m_Nexturrent number of elements in the queue </summary>
		protected internal int m_Size = 0;
		
		//@ public invariant m_Head == null <==> m_Tail == null;
		//@public invariant m_Tail != null ==> m_Tail.m_Next == null;
		//@ public invariant m_Size >= 0;
		//@ public invariant m_Size == 0 <==> m_Head == null;
		//@ public invariant m_Size == 1 <==> m_Head != null && m_Head == m_Tail;
		//@ public invariant m_Size > 1 ==> m_Head != m_Tail;
		//@ public invariant m_Size > 1 <== m_Head != m_Tail;
		
		
		
		/// <summary> Removes all objects from the queue m_Tail.m_Next.</summary>
		//@ assignable m_Size, m_Head, m_Tail;
		//@ ensures m_Size == 0;
		//@ ensures m_Head == null;
		//@ ensures m_Tail == null;
		//UPGRADE_NOTE: Synchronized keyword was removed from method 'removeAllElements'. Lock expression was added. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1027'"
		public void  removeAllElements()
		{
			lock (this)
			{
				m_Size = 0;
				m_Head = null;
				m_Tail = null;
			}
		}
		
		/// <summary> Appends an object to the back of the queue.
		/// 
		/// </summary>
		/// <param name="Item">the object to be appended
		/// </param>
		/// <returns> the object appended
		/// </returns>
		//@ requires Item != null;
		//@ assignable m_Head, m_Tail, m_Tail.m_Next, m_Head.m_Next, m_Size;
		//@ ensures m_Head != null;
		//@ ensures m_Tail != \old(m_Tail);
		//@ ensures m_Size == \old(m_Size) + 1;
		//@ ensures \old(m_Size) == 0 ==> m_Head == m_Tail; 
		//@ ensures \old(m_Size) != 0 ==> m_Head == \old(m_Head);
		//@ ensures m_Tail.contents() == \old(Item);
		//@ ensures \result == Item;
		//UPGRADE_NOTE: Synchronized keyword was removed from method 'push'. Lock expression was added. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1027'"
		public virtual System.Object push(System.Object Item)
		{
			lock (this)
			{
				QueueXmlNode newXmlNode = new QueueXmlNode(this, Item);
				
				if (m_Head == null)
				{
					m_Head = m_Tail = newXmlNode;
				}
				else
				{
					m_Tail = m_Tail.next(newXmlNode);
				}
				m_Size++;
				return Item;
			}
		}
		
		/// <summary> Pops an object from the front of the queue.
		/// 
		/// </summary>
		/// <returns> the object at the front of the queue
		/// </returns>
		/// <exception cref="RuntimeException">if the queue is empty
		/// </exception>
		//@ assignable m_Head, m_Tail, m_Size;
		//@ ensures m_Size == \old(m_Size) - 1;
		//@ ensures m_Head == \old(m_Head.m_Next);
		//@ ensures m_Head != null ==> m_Tail == \old(m_Tail);
		//@ ensures \result == \old(m_Head.m_Contents);
		//@ signals (RuntimeException) \old(m_Head) == null;
		//UPGRADE_NOTE: Synchronized keyword was removed from method 'pop'. Lock expression was added. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1027'"
		public virtual System.Object pop()
		{
			lock (this)
			{
				if (m_Head == null)
				{
					throw new System.SystemException("Queue is empty");
				}
				System.Object retval = m_Head.contents();
				m_Size--;
				m_Head = m_Head.next();
				// Here we need to either tell ESC/Java some facts about
				// the contents of the list after popping off the head,
				// or turn off the 'invariant' warnings.
				//
				//@ assume m_Size == 0 <==> m_Head == null;
				//@ assume m_Size == 1 <==> m_Head == m_Tail;
				if (m_Head == null)
				{
					m_Tail = null;
				}
				return retval;
			}
		}
		
		/// <summary> Gets object from the front of the queue.
		/// 
		/// </summary>
		/// <returns> the object at the front of the queue
		/// </returns>
		/// <exception cref="RuntimeException">if the queue is empty
		/// </exception>
		//@ ensures \result == \old(m_Head.m_Contents);
		//@ signals (RuntimeException) \old(m_Head) == null;
		//UPGRADE_NOTE: Synchronized keyword was removed from method 'peek'. Lock expression was added. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1027'"
		public virtual System.Object peek()
		{
			lock (this)
			{
				if (m_Head == null)
				{
					throw new System.SystemException("Queue is empty");
				}
				return m_Head.contents();
			}
		}
		
		/// <summary> Checks if queue is empty.
		/// 
		/// </summary>
		/// <returns> true if queue is empty
		/// </returns>
		//@ ensures \result <==> m_Head == null;
		public virtual bool empty()
		{
			return m_Head == null;
		}
		
		/// <summary> Gets queue's size.
		/// 
		/// </summary>
		/// <returns> size of queue
		/// </returns>
		//@ ensures \result == m_Size;
		public virtual int size()
		{
			return m_Size;
		}
		
		/// <summary> Produces textual description of queue.
		/// 
		/// </summary>
		/// <returns> textual description of queue
		/// </returns>
		//@ also
		//@ ensures \result != null;
		//@ ensures (* \result == textual description of the queue *);
		public override System.String ToString()
		{
			
			System.String retval = "Queue Contents " + m_Size + " elements\n";
			QueueXmlNode current = m_Head;
			if (current == null)
			{
				return retval + "Empty\n";
			}
			else
			{
				while (current != null)
				{
					//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Object.toString' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
					retval += (current.contents().ToString() + "\n"); //@nowarn Modifies;
					current = current.next();
				}
			}
			return retval;
		} //@ nowarn Post;
		
		/// <summary> Main method for testing this class.
		/// 
		/// </summary>
		/// <param name="argv">a set of strings that are pushed on a test queue
		/// </param>
		//@ requires argv.length >= 0;
		//@ requires argv != null;
		//@ requires (\forall int i; 0 <= i && i < argv.length; argv[i] != null);
		//	public static void main(String [] argv) 
		//	{
		//		try 
		//		{
		//			Queue queue = new Queue();
		//			for(int i = 0; i < argv.length; i++) 
		//			{
		//				queue.push(argv[i]);
		//			}
		//			System.out.println("After pushing command line arguments");
		//			System.out.println(queue.toString());
		//			while (!queue.empty()) 
		//			{
		//				System.out.println("Pop: " + queue.pop().toString());
		//			}
		//			// try one more pop, to make sure we get an exception
		//			try 
		//			{
		//				queue.pop();
		//				System.out.println("ERROR: pop did not throw exception!");
		//			}
		//			catch (RuntimeException ex)
		//			{
		//				System.out.println("Pop on empty queue correctly gave exception.");
		//			}
		//		} 
		//		catch (Exception ex) 
		//		{
		//			System.out.println(ex.getMessage());
		//		}
		//	}
	}
}