namespace HousenCS.Net
{  
	using System;
	using System.ComponentModel;
	using System.Net;
	using System.Net.Sockets;
	using System.Threading;
	using System.Text;

	// UDPServer looks for input on a specified UDP port and raises an event when
	// input is detected. It can also be used to transmit messages to a remote UDP
	// host (such as another UDPServer).

	/// <summary>
	/// 
	/// </summary>
	public class UDPServer 
	{  
		private UdpClient udpClient = null; 

		/// <summary>
		/// 
		/// </summary>
		public Thread receiveThread = null;
		private int localPort = 0;
		private bool stop = false;
		
		/// <summary>
		/// 
		/// </summary>
		/// <param name="aPort"></param>
		public UDPServer(int aPort) 
		{ 
			try 
			{ 
				// Open a UDP connection with the port # specified by the user of this class.
				// This is the port that incoming data from other machines will use.
				localPort = aPort;
				this.udpClient = new UdpClient(localPort);
			} 
			catch (Exception f) 
			{ 
				Console.WriteLine (f.ToString ());
				throw(f);
			} 
		} 

		/// <summary>
		/// 
		/// </summary>
		public void StartListen() 
		{ 
			this.receiveThread = new Thread(new ThreadStart(this.Run)); 
			// this.receiveThread.IsBackground = true;
			this.receiveThread.Start();
		} 

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aHost"></param>
		/// <param name="aPort"></param>
		/// <param name="aMessage"></param>
		/// <returns></returns>
		public string Transmit(string aHost, int aPort, string aMessage)
		{
			Byte[] sendBytes = Encoding.ASCII.GetBytes(aMessage);
			try
			{
				IPEndPoint remoteEndPoint = new IPEndPoint(IPAddress.Parse(aHost), aPort);
				udpClient.Send(sendBytes, sendBytes.Length, remoteEndPoint);
				return ("OK");
			}
			catch (Exception f)
			{
				return (f.ToString());    
			}
		}

		private void Run() 
		{ 
			IPEndPoint localEP = new IPEndPoint(IPAddress.Any, localPort);
			while(!stop) 
			{ 
				try 
				{ 
					byte[] buffer = this.udpClient.Receive(ref localEP); 					
					string bufferString = null;
					for (int i = 0; i < buffer.Length; i++)
					{
						bufferString += (char)buffer[i];
					}
					if (bufferString.Length > 0) 
					{
						InputDetectedEventArgs e = new InputDetectedEventArgs(bufferString);
						OnInputDetected(e);
					}
				} 
				catch (Exception f) 
				{ 
					throw(f);
				} 
			}
			Console.WriteLine ("Stop UDP");
			this.udpClient.Close();
		} 

		// Stop property indicates whether the UDPServer should be turned off.
		/// <summary>
		/// 
		/// </summary>
		public bool Stop 
		{
			get {return stop;}
			set {stop = value;}
		}
      
		// The event member InputDetectedEventHandler.
		/// <summary>
		/// 
		/// </summary>
		public event InputDetectedEventHandler InputDetected;

		// The protected OnInputDetected method raises the event by invoking 
		// the delegates. The sender is always "this", the current instance 
		// of the class.
		/// <summary>
		/// 
		/// </summary>
		/// <param name="e"></param>
		protected virtual void OnInputDetected(InputDetectedEventArgs e)
		{
			if (InputDetected != null) 
			{
				// Invokes the delegates. 
				InputDetected(this, e);
			}
		}
	}


	/// <summary>
	/// Delegate declaration.
	/// </summary>
	public delegate void InputDetectedEventHandler(object sender, InputDetectedEventArgs e);

	
	/// <summary>
	/// InputDetectedEventArgs contains the data for the InputDetected event.
	/// Derives from System.EventArgs.
	/// </summary>
	public class InputDetectedEventArgs : EventArgs 
	{  
		private readonly string inputString;

		/// <summary>
		/// 
		/// </summary>
		/// <param name="inputString"></param>
		public InputDetectedEventArgs(string inputString)
		{
			this.inputString = inputString;
		}

		/// <summary>
		/// 
		/// </summary>
		public string InputString 
		{
			get {return (inputString);}
		}  
	}
}