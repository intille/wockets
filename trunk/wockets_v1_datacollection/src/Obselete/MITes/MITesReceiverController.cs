using System;
using System.Runtime.InteropServices;
using HousenCS.IO;
using HousenCS.SerialIO;
using System.Threading;

namespace HousenCS.MITes
{
	/// <summary>
	/// A MITesReceiverController is used to send/receive data from a MITes Receiver. It creates a SerialPortController
	/// and has some useful wrapper functions. 
	/// </summary>
	public class MITesReceiverController
	{
		private SerialPortController spc = null; 
		private static bool DEBUG = true;
		private static bool PRINT_WARNINGS = true; // For TestPort
	
		private static int MAX_PORT_NUM = 16;

		private static bool isRunning = false; 

		/// <summary>
		/// Check if the MITesReceiver Controller is ok with a valid com port 
		/// </summary>
		/// <returns>True if running</returns>
		public bool IsRunning()
		{
			return isRunning;
		}

		/// <summary>
		/// The object will create threads and use (essentially) the default OpenNetCF code (with some minor tweaks). 
		/// </summary>
		public const bool USE_THREADS = true;
		
		/// <summary>
		/// The object will not create a seperate thread and instead simply reads off the serial port directly when polled. 
		/// </summary>
		public const bool NO_THREADS = false; 

		/// <summary>
		/// The maximum number of bytes that can be stored in the buffer used by this
		/// object to store data coming off the serial port. If this value is too low,
		/// then serial port data will be lost. A higher value will consume more memory
		/// on mobile devices, however. It would be useful to optimize this value at 
		/// some point. 
		/// </summary>
		public static int MAXBYTESBUFFER = 4096; 

		/// <summary>
		/// The buffer that actually stores raw serial data acquired from the SerialPortController. 
		/// </summary>
		public byte[] serialBytesBuffer;

		// These values were defined by emunguia and are hard-coded into the receiver
		private static char messageRxChannel = '9';  //message sent to set the receiver channel
		private static char messageRxGetChannels = '0'; // message sent to get the receiver channels
	
		private int portNumber = 1;
		private int numChannels = 0;
		private int numAccelChannels = 0;
		
		/// <summary>
		/// Get the number of the COM port in use 
		/// </summary>
		/// <returns>The number of the COM port. 0 indicates none.</returns>
		public int GetComPortNumber()
		{
			if (isRunning)
				return portNumber; 
			else
				return 0; 
		}

		/// <summary>
		/// Used by other classes when calling MITesReceiverController to indicate 
		/// that no port has been specified and the SPC should look for a good 
		/// port with the MITesReceiver attached when it opens. 
		/// </summary>
		public static int FIND_PORT = -1; 

		/// <summary>
		/// Return the SerialPortController being used by the MITesReceiverController.
		/// </summary>
		/// <returns></returns>
		public SerialPortController GetSerialPortController()
		{
			return spc;
		}

		/// <summary>
		/// Creates an object that can grab and send data to a MITes reciever using a 
		/// SerialPortController. Defaults to MAXBYTESBUFFER buffer size. Prints warnings when buffer overflows occur.
		/// </summary>
		/// <param name="aPortNumber">The com port number to use (e.g., 1 is COM1)</param>
		public MITesReceiverController(int aPortNumber): this(aPortNumber, MAXBYTESBUFFER)//, true, SerialPortController.NO_THREADS)
		{
		}

		/// <summary>
		/// Creates an object that can grab and send data to a MITes reciever using a 
		/// SerialPortController. 
		/// </summary>
		/// <param name="aPortNumber">The com port number to use (e.g., 1 is COM1)</param>
		/// <param name="maxBytesBuffer">The maximum bytes from the serial port that can be stored in the buffer prior to a read. Adjust to smaller values for mobile devices.</param>
		/// <param name="printWarnings">Set to TRUE to print warnings about buffer overflows. A good idea to use.</param>
		/// <param name="isUsingThreads">Serial port using threads.</param>
		public MITesReceiverController(int aPortNumber, int maxBytesBuffer)
		{
			portNumber = aPortNumber;
			serialBytesBuffer = new byte[maxBytesBuffer];
		}

        public void InitializeController(int portNumber, int maxBytesBuffer, bool printWarnings, bool isUsingThreads)
        {

            Console.WriteLine("Receiver found on COM " + portNumber + "!");

            // Checked that port is valid, so go ahead and reopen it. 
            //spc = new SerialPortController(isUsingThreads, printWarnings, maxBytesBuffer);
            Thread.Sleep(1000);
            spc.SetBaudRate(57600);
            spc.SetPort(portNumber);
            spc.SetParity(0); //none
            spc.SetStopBits(1);
            //isRunning = spc.PortOpen();

        }

		/// <summary>
		/// Test if a port has a receiver attached by trying to open and reading data.
		/// </summary>
		/// <param name="portNum">Port to try</param>
		/// <param name="maxBytesBuffer">Maximum buffer size</param>
		/// <returns></returns>
		public bool TestPort(int portNum, int maxBytesBuffer)
		{
			isRunning = true; 

			bool isValid = true;
			bool isOpen = false;

			Console.WriteLine ("Testing PORT: " + portNum);
//            MessageBox.Show("Testing PORT: " + portNum);
	
			// Setup serial port
			SerialPortController spcTest = new SerialPortController(SerialPortController.USE_THREADS,PRINT_WARNINGS,maxBytesBuffer);
			Thread.Sleep(1000);
			spcTest.SetBaudRate(57600);

			if (spcTest.SetPort(portNum))
			{
				spcTest.SetParity(0); //none
				spcTest.SetStopBits(1);
				try 
				{
					spcTest.PortOpen();
					isOpen = true; 
				}
				catch (ApplicationException e)
				{
					e.ToString ();
					isValid = false;
					isOpen = false;					
				}
			}
			else
			{
				isValid = false;
			}

			// If opened, then test if incoming data looks like MITes data for 1 second
			if (isValid)
			{
                //MessageBox.Show("Able to open " + portNum);
				isValid = false;
				byte[] someData = new byte[4000];

				int startTime = Environment.TickCount;
				// Loop for 1 second and wait for a DD 
				while ((Environment.TickCount-startTime) < 1000)
				{
					//					if (spcTest.isNewData())
					//					{
					int j = spcTest.FillBytesBuffer (someData);
					//Console.WriteLine ("Data: " + someData.Length);
					if (j>1)
						for (int i = 0; i < j-1; i++)
							if ((someData[i] == (int) 68) &&
								(someData[i+1] == (int) 68))
								isValid = true;
					//					}
					Thread.Sleep (100);
				}
			}


			// Shutdown
			//if (isOpen)
			//	spcTest.PortClose();
			//spcTest = null;

			//isRunning = false;
            spc = spcTest;
			return isValid;
		}

		private void Debug(String aMsg)
		{
			if (DEBUG)
				Console.WriteLine(aMsg);
		}

		private void Error(String aMsg)
		{
			Console.WriteLine("ERROR in MITesReceiverController: " + aMsg);
		}

		/// <summary>
		/// Properly shutdown a MITesReceiverController.
		/// </summary>
		public void Close()
		{
			if (spc != null)
				spc.PortClose();
		}

		//		/// <summary>
		//		/// Check if the MITes receiver has sent new data since the last time FillBytesBuffer was called.
		//		/// </summary>
		//		/// <returns>True if there is new data to grab.</returns>
		//		public bool IsNewData()
		//		{
		//			return spc.isNewData();
		//		}

		/// <summary>
		/// If there is new data (which should have been checked with a prior call to IsNewData)
		/// then fill the given buffer with the data. 
		/// </summary>
		/// <param name="serialBytesBuffer">The buffer to fill.</param>
		/// <returns>The number of new data bytes.</returns>
		public int FillBytesBuffer(byte[] serialBytesBuffer)
		{
			if (isRunning)
				return spc.FillBytesBuffer(serialBytesBuffer);
			else
			{
				return 0;
				
			}
		}

		private void PrintData(int n, byte[] serialBytesBuffer)
		{	
			//Console.WriteLine("B: ");
			for (int i = 0; i < n; i++)
				if (((char) serialBytesBuffer[i]) != 'D')
					Console.Write(((int) serialBytesBuffer[i]) + " ");
			//Console.WriteLine("");
		}

		/// <summary>
		///Read the active channels from the receiver.  
		/// </summary>
		/// <param name="channel">Int array in which result is stored (length 6).</param>
		/// <returns>Number of channels found.</returns>
		public int ReadChannels(int[] channel)
		{
  

			byte[] b = new byte[1];
			spc.SendData(BitConverter.GetBytes(messageRxGetChannels),1);
			Debug("Receiver get channels sent");
			Thread.Sleep(200);
			bool done = false;
			bool start = false;
			int index = 0; 
			int n;
			int num = 0;
			int startTime = Environment.TickCount;
			while (!done)
			{
          
				if ((Environment.TickCount - startTime) > 3000)
				{
					done = true;
					return -1;
				}
				n = FillBytesBuffer(serialBytesBuffer);
				PrintData(n,serialBytesBuffer);
          
				for (int i = 0; i < n; i++)
				{
					if (start)
					{
						switch (index)
						{
							case 0: 
								if (serialBytesBuffer[i] == ((char) 'C'))
									index++;
								else
									start = false;
								break;
							case 1: 
								if (serialBytesBuffer[i] == ((char) 'H'))
									index++;
								else 
									start = false;
								break;
							case 2: 
								if (serialBytesBuffer[i] == ((char) 'A'))
									index++;
								else 
									start = false;
								break;
							case 3: 
								num = (int) serialBytesBuffer[i];
								index++;
								break;
							case 4: 
								channel[index-4] = (int) serialBytesBuffer[i];
								index++;
								break;
							case 5: 
								channel[index-4] = (int) serialBytesBuffer[i];
								index++;
								break;
							case 6: 
								channel[index-4] = (int) serialBytesBuffer[i];
								index++;
								break;
							case 7: 
								channel[index-4] = (int) serialBytesBuffer[i];
								index++;
								break;
							case 8: 
								channel[index-4] = (int) serialBytesBuffer[i];
								index++;
								break;
							case 9: 
								channel[index-4] = (int) serialBytesBuffer[i];
								index++;
								done = true;
								break;
							default:
								start = false;
								break;
						}
					}
					else if ((serialBytesBuffer[i] != 68) && (serialBytesBuffer[i] == ((char) 'N')))
						start = true;
				}
			}
			Debug("Active channels: " + num);

			for (int i = num; i < 6; i++)
				channel[i] = NO_ID;

			for (int i = 0; i < 6; i++)
				Debug("Channel " + i + ": " + channel[i]);
			SetNumChannels(num,channel);
			return num;
		}

		/// <summary>
		/// Constant indicating that a channel is not being used. 
		/// </summary>
		public const int NO_ID = -1; 

		private void SetNumChannels(int num, int[] channels)
		{
			int total = 0;
			bool isChannel0 = false;
			for (int i = 0; i < 6; i++)
			{
				if ((channels[i] < 0) || (channels[i] > 255))
					Error("Channel out of range: " + channels[i]);
				if (channels[i] != MITesDecoder.STATIC_CHANNEL)
					total++;
				if (channels[i] == MITesDecoder.STATIC_CHANNEL)
					isChannel0 = true;
			}
			numAccelChannels = total;
			numChannels = total; 
			if (isChannel0)
				numChannels += 1; 
		}

		/// <summary>
		/// Returns the number of active channels, including STATIC channel. 
		/// </summary>
		/// <returns></returns>
		public int GetNumChannels()
		{
			return numChannels;
		}

		/// <summary>
		/// Returns the number of active accelerometer channels, not including STATIC channel. 
		/// </summary>
		/// <returns></returns>
		public int GetNumAccelChannels()
		{
			return numAccelChannels;
		}

		private int tmpChannel = 0;
		
		/// <summary>
		/// Set the channels on the receiver. 
		/// </summary>
		/// <param name="num">The number of channels.</param>
		/// <param name="channel">Int array of channel numbers.</param>
		public void SetChannels(int num, int[] channel)
		{
			SetNumChannels(num,channel);
			byte[] b = BitConverter.GetBytes(messageRxChannel);
			Console.WriteLine("Len: " + b.Length);
			spc.SendData(b,1);
			Debug("Receiver channel sent");
			Thread.Sleep(100);   //this timing is extremely IMPORTANT!!! keep the same across machines
			
			// Send number of active channels
			b = new byte[1];
			b[0] = (byte) num;
			spc.SendData(b);
			Debug("Sent n channels: " + num);
			Thread.Sleep(100);   //this timing is extremely IMPORTANT!!! keep the same across machines
		
			// Send channel numbers
			for (int i = 0; i < 6; i++)
			{
				if (channel[i] == NO_ID)
				{
					tmpChannel = 0; 
				}
				else
				{
					if ((channel[i] < 0) || (channel[i] > 255))
						Error("Channel out of range: " + channel[i]);
					else
						tmpChannel = channel[i];
				}
				b[0] = (byte) tmpChannel;
				spc.SendData(b);
				if (channel[i]==NO_ID)
					Debug("Sent channel " + i + ": " + "NONE");
				else
					Debug("Sent channel " + i + ": " + tmpChannel);
				Thread.Sleep(100);   //this timing is extremely IMPORTANT!!! keep the same across machines
			}	
			Debug("Tx/Tx Channel list sent");
		}

		/// <summary>
		/// Test method.
		/// </summary>
		public static void Main()
		{
			long m1;
			long m2;

			m1 = GC.GetTotalMemory(false);
			MITesData[] md = new MITesData[10000];
			for (int i = 0; i < 10000; i++)
				md[i] = new MITesData();
			m2 = GC.GetTotalMemory(false); 

			Console.WriteLine("Size: " + (m2-m1));

			Thread.Sleep (10000);

		}
	}
}

//			MITesReceiverController mrc = new MITesReceiverController();
//			MITesReceiverController mrc = new MITesReceiverController(8,2000,true, SerialPortController.USE_THREADS);
//			Thread.Sleep(100);
//			byte[] someBytes = new byte[2000];
//
//			int time = Environment.TickCount;
//
//			int n = 0;
//			int count = 0; 
//			while ((Environment.TickCount - time) < 10000)
//			{
//				if (mrc.IsNewData ())
//				{
//					n = mrc.FillBytesBuffer (someBytes);
//					if (n != 0)
//					{
//						count += n;					
//						Console.WriteLine ("Bytes:" + n);
//					}
//				}
//			}
//			Console.WriteLine ("Total:" + count);
//
//			Thread.Sleep (10000);
//			mrc.Close ();
