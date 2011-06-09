using System;
using System.Threading;
using System.Text;
using OpenNETCF.IO.Serial;

namespace HousenCS.SerialIO
{
	/// <summary>
	/// An object that can be used to easily send and receive data from a serial port. It uses a polling mechanism
	/// for simplicity. This has been tested on desktop, PPC, and SmartPhone devices. There are two modes availabe
	/// for serial port data grabbing: threaded, which is preferred, and non-threaded. Non-threaded is 
	/// simpler code; however, on a PPC and Smartphone, due to a bug in ReadFile, this option will block. 
	/// 
	/// Author: Stephen Intille (intille@mit.edu)
	/// </summary>
	public class SerialPortController
	{
		private bool isThreaded = true; 
		private Port port;
		private DetailedPortSettings portSettings;
		private bool isPrintWarnings = true; 
		private bool running = false;
		private int maxBufferSize = DEFAULT_MAX_BUFFER_SIZE;
		private byte[] bytesBuffer;
		//private long[] bytesBufferTiming;
		private int bytesBufferCount = 0;
		private byte[] inputData = new byte[1];
		private int tempByteCount = 0; 
		private int lostBytes = 0; 
		private int bufferLength = 0;
		private int aveGrab = 0;
		private int numGrabs = 0;

		/// <summary>
		/// If True, thows an ApplicationException on errors. Otherwise, simply prints a 
		/// warning message to the Console.  
		/// </summary>
		public const bool THROW_EXCEPTION_ON_ERROR = true;

		/// <summary>
		/// Used in constructor to indicate that the object will create threads 
		/// and use (essentially) the default OpenNetCF code (with some minor tweaks). 
		/// </summary>
		public const bool USE_THREADS = true;
		
//		/// <summary>
//		/// Used in constructor to indicate that the object will save the 
//		/// precise timing information when every byte of data arrived.  
//		/// </summary>
//		public const bool SAVE_TIMING = true;

		/// <summary>
		/// Used in constructor to indicate that the object will not create a 
		/// seperate thread and instead simply reads off the serial port directly
		/// when polled. This causes blocking on the PPC and Smartphone and is
		/// therefore not the best option at this time. 
		/// </summary>
		public const bool NO_THREADS = false; 
	
		/// <summary>
		/// Default maximum buffer size for the SerialPortController. If data arrives and this buffer
		/// is full data will be lost. Warnings may be printed to the Console if the 
		/// SerialPortController is initialized to print messsages.  
		/// </summary>
		public const int DEFAULT_MAX_BUFFER_SIZE = 4096;
		
		/// <summary>
		/// Constructor for SerialPortController that allows data to be read from and 
		/// written to the serial port.
		/// </summary>
		/// <param name="isThreaded">Determines if the object uses multiple threads (with no blocking) or a single thread (with possible blocking)</param>
		/// <param name="isPrintWarnings">Print warnings to Console when buffers overflow is set to true</param>
		/// <param name="maxBufferSize">The maximum size of the bytes buffer (2048 a good value in practice)</param>
		public SerialPortController(bool isThreaded, bool isPrintWarnings, int maxBufferSize)
		{
			this.isThreaded= isThreaded; 
			this.maxBufferSize = maxBufferSize;
			bytesBuffer = new byte[maxBufferSize];
			//if (SAVE_TIMING)
			//	bytesBufferTiming = new long[maxBufferSize];

			// create the port settings
			portSettings = new HandshakeNone();

			// create a default port on COM2 with no handshaking
			port = new Port("COM1:", portSettings);

			// these are fairly inefficient settings
			// for a terminal we want to send/receive all data as it is queued
			// so 1 byte at a time is the best way to go
			port.RThreshold = 1;	// get an event for every 1 byte received
			port.InputLen = 1;		// calling Input will read 1 byte
			port.SThreshold = 1;	// send 1 byte at a time

			// define an event handler if using threaded option
			if (isThreaded)
				port.DataReceived +=new Port.CommEvent(port_DataReceived);

			this.isPrintWarnings = isPrintWarnings; 
		}

		private void Error(String str)
		{
			String msg = "ERROR in SerialPortController: " + str;
			System.Console.WriteLine(msg);
			if (THROW_EXCEPTION_ON_ERROR)
				throw new ApplicationException(msg);
		}

		private void PrintWarning(String str)
		{
			if (isPrintWarnings)
				System.Console.WriteLine("Warning: " + str);
		}

		/// <summary>
		/// Test if the port given is valid (i.e., can be opened).  
		/// </summary>
		/// <param name="num">Port number (1-12)</param>
		/// <returns>True if possible to open the port</returns>
		private bool TestPort(int num)
		{
			bool isValid = true;
			port.PortName = "COM" + num + ":";

			try
			{
				PortOpen();						
			}
			catch (ApplicationException e)
			{
				e.ToString ();				
				isValid = false;
				return false;
			}
			return isValid;
		}

		/// <summary>
		/// Searches from COM1-COM12 and prints if each port is valid or not (i.e.
		/// can be opened).
		/// </summary>
		public void PrintValidPorts()
		{
			for (int i = 1; i <= 12; i++)
				if (TestPort(i))
					Console.WriteLine ("COM" + i + " VALID");
				else
					Console.WriteLine ("COM" + i + " INVALID");
		}

		/// <summary>
		/// Searches from COM1-COM12 and returns a String indicating which ports
		/// are valid or not (i.e.can be opened). 
		/// </summary>
		/// <returns>The String indicating valid and invalid ports</returns>
		public String GetValidPortsString()
		{
			String strValid = "Valid:";
			String strInValid = "Invalid:";
			for (int i = 1; i <= 12; i++)
				if (TestPort(i))
					strValid += " " + i;
				else
					strInValid += " " + i;
			
			return (strValid + " " + strInValid); 
		}

		/// <summary>
		/// Return the string name of the serial port in use (e.g. "COM1:")
		/// </summary>
		/// <returns>String port name</returns>
		public String GetPort()
		{
			return port.PortName;
		}

        public void SetPort(string portName)
        {
            port.PortName = portName;
        }
		/// <summary>
		/// Set the COM port to use. Must be called before Open.
		/// </summary>
		/// <param name="portNumber">A number of the port (e.g., 1 is COM1)</param>
		/// <returns>True if set port, false if invalid port</returns>
		public bool SetPort(int portNumber)
		{	if (portNumber == 0)
                port.PortName = "COM0:";
			else if (portNumber == 1)
				port.PortName = "COM1:";
			else if (portNumber == 2)
				port.PortName = "COM2:";
			else if (portNumber == 3)
				port.PortName = "COM3:";
			else if (portNumber == 4)
				port.PortName = "COM4:";
			else if (portNumber == 5)
				port.PortName = "COM5:";
			else if (portNumber == 6)
				port.PortName = "COM6:";
			else if (portNumber == 7)
				port.PortName = "COM7:";
			else if (portNumber == 8)
				port.PortName = "COM8:";
			else if (portNumber == 9)
				port.PortName = "COM9:";
			else if (portNumber == 10)
				port.PortName = "COM10:";
			else if (portNumber == 11)
				port.PortName = "COM11:";
			else if (portNumber == 12)
				port.PortName = "COM12:";
			else if (portNumber == 13)
				port.PortName = "COM13:";
			else if (portNumber == 14)
				port.PortName = "COM14:";
			else if (portNumber == 15)
				port.PortName = "COM15:";
			else if (portNumber == 16)
				port.PortName = "COM16:";
			else if (portNumber == 17)
				port.PortName = "COM17:";
			else if (portNumber == 18)
				port.PortName = "COM18:";
			else
			{
				Error(portNumber + " *** is not a valid port.");
				return false; 
			}
			return true;
		}
	
		/// <summary>
		/// Set the baud rate on the serial port. Must be called before Open.
		/// </summary>
		/// <param name="baudRate">Baudrate to set (4800,9600,14400,19200,57600)</param>
		public void SetBaudRate(int baudRate)
		{
			if (baudRate == 4800)
				port.Settings.BaudRate = BaudRates.CBR_4800;
			else if (baudRate == 9600)
				port.Settings.BaudRate = BaudRates.CBR_9600;
			else if (baudRate == 14400)
				port.Settings.BaudRate = BaudRates.CBR_14400;
			else if (baudRate == 19200)
				port.Settings.BaudRate = BaudRates.CBR_19200;
			else if (baudRate == 57600)
				port.Settings.BaudRate = BaudRates.CBR_57600;
			else
			{
				Error(baudRate + " is not a valid baudrate. Defaulting to 4800");
				port.Settings.BaudRate = BaudRates.CBR_4800;
			}												
		}

		/// <summary>
		/// Set the serial port parity to use. Must be called before Open.
		/// </summary>
		/// <param name="parityValue">Parity.odd, Parity.none, or Parity.even</param>
		public void SetParity(int parityValue)
		{
			if (parityValue == 1)
				port.Settings.Parity = Parity.odd;
			else if (parityValue == 0)
				port.Settings.Parity = Parity.none;
			else if (parityValue == 2)
				port.Settings.Parity = Parity.even;
			else 
			{
				Error(parityValue + " is not valid (1/0). Defaulting to even.");
				port.Settings.Parity = Parity.even;
			}
		}
					
		/// <summary>
		/// Set the stop bits on the serial port. Must be called before Open.
		/// </summary>
		/// <param name="stopBits">StopBits.one or StopBits.two</param>
		public void SetStopBits(int stopBits)
		{
			if (stopBits == 1)
				port.Settings.StopBits = StopBits.one;
			else if (stopBits == 2)
				port.Settings.StopBits = StopBits.two;
			else 
			{
				Error(stopBits + " is not valid (1/2). Defaulting to one.");
				port.Settings.StopBits = StopBits.two;
			}
		}

        public void SetDCB()
        {
            try
            {
                port.SetDCB();
            }
            catch
            {
                running = false;
                Error("The serial port cannot be opened. Reset device.");
            }
        }
		/// <summary>
		/// Open the serial port (threaded or blocking, depending on how SerialPortController
		/// was initialized. 
		/// </summary>
		/// <returns>True if succeeded</returns>
		public bool PortOpen()
		{
			try
			{
				port.OpenThreaded(isThreaded);
				running = true;
			}
			catch
			{
				running = false;
				Error("The serial port cannot be opened. Reset device.");
			}
			return running; 
		}

		/// <summary>
		/// Close the SPC. 
		/// </summary>
		public void PortClose()
		{
			running = false;
			Thread.Sleep(100);
			port.Close();
		}

		/// <summary>
		/// Send byte data to the serial port. Note: this has not been tested for sending large
		/// amounts of data. Also, this has only been tested with the threaded option. 
		/// </summary>
		/// <param name="outputData">Array of byte data to send</param>
		/// <param name="n">Number of bytes from array</param>
		public void SendData(byte[] outputData, int n)
		{
			if (running)
			{
				byte[] data = new byte[1];
			
				if (n > outputData.Length)
					PrintWarning("SendData byte array too short");

				for (int i = 0; i < Math.Min(n,outputData.Length); i++)
				{
					data[0] = outputData[i]; 
					port.Output = data;
					Thread.Sleep(0);
				}
			}
			else
			{
				Error("Can't sendData. Port not open.");
			}
		}

		/// <summary>
		/// Send byte data to the serial port. 
		/// </summary>
		/// <param name="outputData">The array of bytes to send</param>
		public void SendData(byte[] outputData)
		{
			SendData(outputData, outputData.Length);
		}

		/// <summary>
		/// Send String data to the serial port.
		/// </summary>
		/// <param name="outputString">String to send</param>
		public void SendTextData(string outputString)
		{
			if (running)
			{
				byte[] outputData = new byte[1];

				for(int i = 0 ; i < outputString.Length ; i++)
				{
					outputData[0] = Convert.ToByte(outputString[i]);
					port.Output = outputData;
				}
			}
			else
			{
				Error("Can't sendTextData. Port not open.");
			}
		}

		/// <summary>
		/// Key method that grabs data from the serial port.
		/// </summary>
		/// <param name="retBytes">An allocated array of bytes in which the data is placed</param>
		/// <returns>The number of new bytes grabbed from the serial port</returns>
		public int FillBytesBuffer(byte[] retBytes)
		{
			int i = 0; 
			if (running)
			{
				if (isThreaded)
				{
					i = FillBytesBufferThreaded(retBytes);
				}
				else
				{
					i = port.GrabData(retBytes);
				}
			}
			return i;
		}

        int previousTick=0, nodataMilliseconds = 0;
        public static int TIMEOUT_WITHOUT_DATA = 5000;
        private bool receivedData = false;
		private int FillBytesBufferThreaded(byte[] retBytes)
		{
 
            
			if (IsNewData())
			{
				if (retBytes.Length < bytesBufferCount)
					PrintWarning("FillBytesBuffer too small by " + (bytesBufferCount-retBytes.Length) + "! (size buffer: " + bytesBufferCount +", size storage:" + retBytes.Length+")");

				for (int i = 0; i < bytesBufferCount; i++)
				{
					if (i < retBytes.Length)
						retBytes[i] = bytesBuffer[i];
                                   
				}

				if (bytesBufferCount > retBytes.Length)
					tempByteCount = retBytes.Length;
				else
					tempByteCount = bytesBufferCount;
				bytesBufferCount = 0;
                
  
                nodataMilliseconds = 0;
                previousTick = Environment.TickCount;
                receivedData = true;
				return tempByteCount;
			}
			else
			{
#if (PocketPC)
                if (receivedData)
                {
                    nodataMilliseconds += nodataMilliseconds + (Environment.TickCount - previousTick);
                    if (nodataMilliseconds > TIMEOUT_WITHOUT_DATA)
                        throw new ConnectionException("No receiver data for 5 seconds");
                    previousTick = Environment.TickCount;
                }
#endif
                //PrintWarning("No data to get!");
				return 0;
			}
                        
		}

		private bool IsNewData()
		{
			if (bytesBufferCount == 0)
				return false;
			else
				return true;
		}

//		private long timeDataReceived = 0;

		private void port_DataReceived()
		{
			if (running)
			{
				while (port.InBufferCount != 0)
				{
					lostBytes = 0;

//					if (SAVE_TIMING)
//						timeDataReceived = InputTimer.GetSystemTimeMS();

					//InBufferCount contains the number of bytes pending on the serial buffer
					bufferLength = port.InBufferCount;

					aveGrab += bufferLength;
					numGrabs += 1;

					// I think this leads to lag in the current code. Best not to do it. 

					//					// If there's more then 200 bytes, i process the first 200 and the rest will be processed next time
					//					if (bufferLength > 200) 
					//					{
					//						bufferLength = 200;
					//					}

					for (int i = 0; i < bufferLength; i++)
					{
						inputData = port.Input;
						if (bytesBufferCount < maxBufferSize)
						{
							bytesBuffer[bytesBufferCount] = inputData[0];
//							if (SAVE_TIMING)
//								bytesBufferTiming[bytesBufferCount] = timeDataReceived;
							bytesBufferCount++;
						}
						else
							lostBytes++;
					}
					if (lostBytes > 0)
					{
						PrintWarning("Serial buffer of size " + maxBufferSize + " got full. Lost data: " + lostBytes + "bytes!");
						ClearPort();
						return;
					}
				}
				Thread.Sleep(0);
			}
		}

		private void ClearPort()
		{
			if (running)
			{
				while (port.InBufferCount != 0)
				{
					inputData = port.Input;
					Thread.Sleep(0);
				}
				bytesBufferCount = 0;
			}
		}

		/// <summary>
		/// Test method.
		/// </summary>
		public static void Main()
		{
			int bytesBufferSize = 2048; 
			bool isPrintWarnings = true; 

			// Works on the PC, PPC 
			//SerialPortController spc = new SerialPortController(SerialPortController.NO_THREADS, isPrintWarnings, bytesBufferSize);
		
			// Works on the PC, PPC
			SerialPortController spc = new SerialPortController(SerialPortController.USE_THREADS, isPrintWarnings, bytesBufferSize);

			Thread.Sleep(100);

			//PPC casing serial: 1, bluetooth 5
			//Smartphone serial: 6

			if (spc.SetPort(1))
				Console.WriteLine ("Set port successfully");
			else
			{
				Console.WriteLine ("Could not set port number");
				//Application.Exit();
			}

			//spc.SetBaudRate(57600);
			spc.SetBaudRate(9600);
			spc.SetParity(0); //none
			spc.SetStopBits(1);
			spc.PortOpen();

			long time = Environment.TickCount;

			byte[] serialBytesBuffer = new byte[bytesBufferSize];
			int bytesFound;
			byte v = (byte) 0;

			int total = 0; 
			Console.WriteLine("Serial");
			spc.ClearPort();

			int ave = 0; 
			int count = 0;

			int sleepval = 10; 
			time = Environment.TickCount;
			ave = 0; 
			count = 0;
			Console.WriteLine("");
			Console.WriteLine("Testing sleep of " + sleepval);
			while ((Environment.TickCount - time) < 60000)
			{
				bytesFound = spc.FillBytesBuffer(serialBytesBuffer);

//				if ((bytesFound != 0) || ((count % 1000) == 0))
//					Console.WriteLine ("Bytes: " + bytesFound + "total: " + total + " Count: " + count);

				total += bytesFound;
				ave += bytesFound;
				count++; 

				for (int i = 0; i < bytesFound; i++)
				{
					v = serialBytesBuffer[i];
					Console.WriteLine (v);
				}
				Thread.Sleep(sleepval);
			}
			Console.WriteLine("Total: " + total);
			Console.WriteLine("Ave chunk: " + (ave/((double)count)));
			Thread.Sleep(10000);
			
			spc.PortClose();
		}
	}
}
