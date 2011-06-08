using System;
using System.Collections;

namespace weka.support
{
	
	public interface ITree
	{
		Node FirstNode();
		System.String DescriptionTree();
	}
	public class Node
	{
		public System.String Name;
		public ArrayList childs;
		public ArrayList conectionNames;
		
		public Node(System.String aName)
		{
			Name = aName;
			childs = new ArrayList();
			conectionNames = new ArrayList();
		}
		public virtual void  AddChild(System.String ConectionName, Node child)
		{
			childs.Add(child);
			conectionNames.Add(ConectionName);
		}
	}
}