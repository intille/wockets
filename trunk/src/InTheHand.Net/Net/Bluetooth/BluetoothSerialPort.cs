// 32feet.NET - Personal Area Networking for .NET
//
// InTheHand.Net.Ports.BluetoothSerialPort
// 
// Copyright (c) 2003-2006 In The Hand Ltd, All rights reserved.
// This source code is licensed under the In The Hand Community License - see License.txt

using System;
using System.Net;
using System.ComponentModel;
using System.Runtime.InteropServices;
using InTheHand.Net.Bluetooth;
using InTheHand.Net;

namespace InTheHand.Net.Ports
{
	/// <summary>
	/// Represents a virtual COM port.
	/// </summary>
	public class BluetoothSerialPort : IDisposable
	{
		private string portPrefix;
		private int portIndex;
		private PORTEMUPortParams pep;
		private IntPtr handle;

		internal BluetoothSerialPort(string portPrefix, int portIndex)
		{
			pep = new PORTEMUPortParams();
			this.portPrefix = portPrefix;
			this.portIndex = portIndex;
		}

		private void Register()
		{
			GC.KeepAlive(this);

			handle = RegisterDevice(portPrefix, portIndex, "btd.dll", pep.ToByteArray());

			if(handle == IntPtr.Zero)
			{
				int error = Marshal.GetLastWin32Error();
				throw new Win32Exception(error, "Error creating virtual com port");
			}
		}

		/// <summary>
		/// Create a virtual server port to listen for incoming connections.
		/// </summary>
		/// <param name="portName">Port name e.g. "COM4"</param>
		/// <param name="service">Bluetooth service to listen on.</param>
		/// <returns></returns>
		public static BluetoothSerialPort CreateServer(string portName, Guid service)
		{
            string portPrefix;
            int portIndex;
            SplitPortName(portName, out portPrefix, out portIndex);

			BluetoothSerialPort bsp = new BluetoothSerialPort(portPrefix, portIndex);
			bsp.pep.Local = true;
			bsp.pep.Service = service;
			bsp.Register();
			return bsp;
		}

        /// <summary>
        /// Create a virtual server port to listen for incoming connections. Auto allocates a port from the COM0-9 range.
        /// </summary>
        /// <param name="service">Service GUID to listen on.</param>
        /// <returns></returns>
        public static BluetoothSerialPort CreateServer(Guid service)
        {
            BluetoothSerialPort bsp = new BluetoothSerialPort("COM", 9);
            bsp.pep.Local = true;
            bsp.pep.Service = service;
            for (int iPort = 8; iPort > -1; iPort--)
            {
                try
                {
                    bsp.Register();
                    break;
                }
                catch
                {
                    bsp.portIndex = iPort;
                }
            }
            return bsp;
        }

		/// <summary>
		/// Create a client port for connection to a remote device.
		/// </summary>
		/// <param name="portPrefix">Port name e.g. "COM4"</param>
		/// <param name="endPoint">Remote device to connect to</param>
		/// <returns>A BluetoothSerialPort.</returns>
		public static BluetoothSerialPort CreateClient(string portName, BluetoothEndPoint endPoint)
		{
            string portPrefix;
            int portIndex;
            SplitPortName(portName, out portPrefix, out portIndex);
			BluetoothSerialPort bsp = new BluetoothSerialPort(portPrefix, portIndex);
			bsp.pep.Local = false;
			bsp.pep.Address = endPoint.Address;
			bsp.pep.Service = endPoint.Service;

            bsp.Register();

			return bsp;
		}
        /// <summary>
        /// Create a client port for connection to a remote device.  Auto allocates a port from the COM0-9 range.
        /// </summary>
        /// <param name="endPoint">Remote device to connect to.</param>
        /// <returns></returns>
        public static BluetoothSerialPort CreateClient(BluetoothEndPoint endPoint)
        {
            BluetoothSerialPort bsp = new BluetoothSerialPort("COM", 9);
            bsp.pep.Local = false;
            bsp.pep.Address = endPoint.Address;
            bsp.pep.Service = endPoint.Service;
            
            for (int iPort = 8; iPort > -1; iPort--)
            {
                try
                {
                    bsp.Register();
                    break;
                }
                catch
                {
                    bsp.portIndex = iPort;
                }
            }
            return bsp;
        }

        /// <summary>
        /// Creates a BluetoothSerialPort instance from an existing open virtual serial port handle.
        /// </summary>
        /// <param name="handle">Handle value created previously by BluetoothSerialPort.</param>
        /// <returns>BluetoothSerialPort wrapper around handle.</returns>
        public static BluetoothSerialPort FromHandle(IntPtr handle)
        {
            BluetoothSerialPort bsp = new BluetoothSerialPort("COM", 0);
            bsp.handle = handle;
            return bsp;
        }

		/// <summary>
		/// The full representation of the port name e.g. "COM5"
		/// </summary>
		public string PortName
		{
			get
			{
				return portPrefix + portIndex.ToString();
			}
		}

        private static void SplitPortName(string portName, out string prefix, out int index)
        {
            if (portName.Length < 4)
            {
                throw new ArgumentException("Invalid Port Name");
            }
            prefix = portName.Substring(0, 3);
            index = Int32.Parse(portName.Substring(3,1));
        }

		/// <summary>
		/// The address of the remote device to which this port will connect (Client Ports only).
		/// </summary>
		public BluetoothAddress Address
		{
			get
			{
				return pep.Address;
			}
		}

		/// <summary>
		/// The Bluetooth service to connect to.
		/// </summary>
		public Guid Service
		{
			get
			{
				return pep.Service;
			}
		}

		/// <summary>
		/// Specifies whether the port is a local service or for outgoing connections.
		/// </summary>
		/// <value>TRUE for a server port that accepts connections, or to FALSE for a client port that is used to creating outgoing connections.</value>
		public bool Local
		{
			get
			{
				return pep.Local;
			}
		}

        /// <summary>
        /// Native handle to virtual port.
        /// </summary>
        public IntPtr Handle
        {
            get
            {
                return this.handle;
            }
        }

		/// <summary>
		/// Closes the virtual serial port releasing all resources.
		/// </summary>
		public void Close()
		{
			GC.KeepAlive(this);

			if(handle != IntPtr.Zero)
			{
				bool success = DeregisterDevice(handle);

				if(success)
				{
					handle = IntPtr.Zero;
				}
				else
				{
					throw new SystemException("Error deregistering virtual COM port " + Marshal.GetLastWin32Error().ToString("X"));
				}
			}
		}

		[DllImport("coredll.dll", SetLastError=true)]
		private static extern IntPtr RegisterDevice(
			string lpszType,
			int	dwIndex,
			string lpszLib,
			byte[]	dwInfo);

		[DllImport("coredll.dll", SetLastError=true)]
		private static extern bool DeregisterDevice(
			IntPtr handle);

		#region IDisposable Members

		/// <summary>
		/// 
		/// </summary>
		/// <param name="disposing"></param>
		protected virtual void Dispose(bool disposing)
		{
			Close();

			if(disposing)
			{
				portPrefix = null;
				pep = null;
			}
		}

		/// <summary>
		/// 
		/// </summary>
		public void Dispose()
		{
			Dispose(true);
			GC.SuppressFinalize(this);
		}

		/// <summary>
		/// 
		/// </summary>
		~BluetoothSerialPort()
		{
			Dispose(false);
		}

		#endregion
	}
}
