using System;
using System.Collections.Generic;
using System.Text;
using System.Collections;
using Microsoft.Win32; 

namespace Wockets.Utils.network.Bluetooth
{
    /// <summary>
    /// An abstract class that defines a unified interface for the Bluetooth stack. The class can be extended to support
    /// any bluetooth stack
    /// </summary>
    public abstract class BluetoothStack
    {

        /// <summary>
        /// Defines the type of the Bluetooth stack
        /// </summary>
        private static BluetoothStackTypes type;

        /// <summary>
        /// Stores references to all active serial bluetooth connections
        /// </summary>
        protected Hashtable bluetoothStreams;

        /// <summary>
        /// Initializes the status of the bluetooth stack
        /// </summary>
        public BluetoothStack()
        {
            this.bluetoothStreams = new Hashtable();            
        }


        /// <summary>
        /// The read-only property returns the type of Bluetooth stack. At the moment, Microsoft and Widcomm stacks are supported
        /// </summary>
        public static BluetoothStackTypes _Type
        {
            get
            {
                //Determine the type of Bluetooth Stack
                RegistryKey rk = Registry.LocalMachine.OpenSubKey("Software\\Microsoft\\Bluetooth\\");
                RegistryKey rk2 = Registry.LocalMachine.OpenSubKey("Software\\WIDCOMM\\Applications");
                if (rk2 != null)
                    type = BluetoothStackTypes.Widcomm;

                else 
                if (rk != null)
                    type = BluetoothStackTypes.Microsoft;
                else
                {
                    rk = null;
                    rk = Registry.LocalMachine.OpenSubKey("Software\\WIDCOMM\\");
                    if (rk != null)
                        type = BluetoothStackTypes.Widcomm;
                    else
                        type = BluetoothStackTypes.Microsoft;
                }
                return type;
            }
        }

 
        /// <summary>
        /// An abstract method that initializes the stack
        /// </summary>
        /// <returns>True on success, otherwise false</returns>
        public abstract bool Initialize();

        /// <summary>
        /// An abstract method that discovers Bluetooth devices
        /// </summary>
        /// <returns>A hashtable of discoverable bluetooth devices</returns>
        public abstract Hashtable Search();

        /// <summary>
        /// An abstract method that requests a serial connection from the Bluetooth stack
        /// </summary>
        /// <param name="buffer">A reference to a receive buffer where the data is read from the stream</param>
        /// <param name="sbuffer">A reference to a send buffer where data is written to the stream</param>
        /// <param name="address">Address of the remote bluetooth host</param>
        /// <param name="pin">Pin for the remote bluetooth host</param>
        /// <returns>A bluetoothstream object on success, otherwise null</returns>
        public abstract BluetoothStream Connect(CircularBuffer buffer,CircularBuffer sbuffer, byte[] address, string pin);

        /// <summary>
        /// An abstract method that disposes and releases any resources associated with the Bluetooth stack
        /// </summary>
        public abstract void Dispose();
    }
}
