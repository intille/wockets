using System;
using System.Drawing;
using System.Collections;
using System.ComponentModel;
using System.Threading;
using System.Windows.Forms;
using System.Data;
using System.Net;
using System.Net.Sockets;

namespace SocketServer
{
	/// <summary>
	/// Summary description for SocketTransmitter.
	/// </summary>
	public class SocketTransmitter
	{
		//		public AsyncCallback pfnWorkerCallBack ;
		private Socket s;

		//		private bool isOpen = false;
		private int portNum = 8221;

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aPortNum"></param>
		public SocketTransmitter(int aPortNum)
		{
			this.portNum = aPortNum;
			Initialize(portNum);
		}

		private void Initialize(int portNum)
		{
			try
			{
				//create the listening socket...
				s = new Socket(AddressFamily.InterNetwork,SocketType.Dgram,ProtocolType.Udp);
				IPAddress ip=IPAddress.Parse("127.0.0.1");
				IPEndPoint ipep=new IPEndPoint(ip, portNum);
				IPEndPoint ipLocal = new IPEndPoint ( ip ,portNum);
				s.Connect(ipep);
				//isOpen = true;
			}
			catch(SocketException se)
			{
				//isOpen = false;
				Console.WriteLine ( se.Message );
			}
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="txtDataTx"></param>
		public void SendData(string txtDataTx)
		{
			try
			{
				Object objData = txtDataTx;
				byte[] byData = System.Text.Encoding.ASCII.GetBytes(objData.ToString ());
				if (s != null)
					s.Send (byData);
				else
					Console.WriteLine ("NULL");
			}
			catch(SocketException se)
			{
				Console.WriteLine (se.Message);
			}
		}

		/// <summary>
		/// 
		/// </summary>
		public class CSocketPacket
		{
			/// <summary>
			/// 
			/// </summary>
			public System.Net.Sockets.Socket thisSocket;
			
			/// <summary>
			/// 
			/// </summary>
			public byte[] dataBuffer = new byte[1];
		}

		/// <summary>
		/// 
		/// </summary>
		static void Main() 
		{
			SocketTransmitter st = new SocketTransmitter(8221);
			int count = 0;
			while (true)
			{
				count++;
				Console.WriteLine ("Test");
				st.SendData(Environment.TickCount + " " + "ON");
				Thread.Sleep(1000);
			}
		}

	}
}
