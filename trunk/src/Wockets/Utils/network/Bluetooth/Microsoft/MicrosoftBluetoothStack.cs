using System;
using System.Collections.Generic;
using System.Text;
using System.Collections;
using System.Runtime.InteropServices;
using Wockets.Utils.network.Bluetooth;

#if (!PocketPC)

// 32.feet.NET references
using InTheHand.Net;
using InTheHand.Net.Sockets;
using InTheHand.Net.Bluetooth;

#endif

namespace Wockets.Utils.network.Bluetooth.Microsoft
{
    public class MicrosoftBluetoothStack : BluetoothStack
    {
#if (PocketPC)
        public enum RadioMode
        {
            /// <summary>
            /// Bluetooth is disabled on the device.
            /// </summary>
            PowerOff,
            /// <summary>
            /// Bluetooth is connectable but your device cannot be discovered by other devices.
            /// </summary>
            Connectable,
            /// <summary>
            /// Bluetooth is activated and fully discoverable.
            /// </summary>
            Discoverable,
        }

        
        [DllImport("BthUtil.dll", SetLastError = true)]
        public static extern int BthSetMode(RadioMode dwMode);

        [DllImport("BthUtil.dll", SetLastError = true)]
        public static extern int BthGetMode(out RadioMode dwMode);
#endif



        /// <summary>
        /// The constructor intializes the state of the Bluetooth stack to On
        /// </summary>
        public MicrosoftBluetoothStack()
        {
            this.Mode = RadioMode.PowerOff;
            //this.Mode = RadioMode.Connectable;
        }

        /// <summary>
        /// Change the status of the Bluetooth stack, connectable, discoverable or off
        /// </summary>
        public RadioMode Mode
        {
            get
            {

#if (PocketPC)
				RadioMode val;
				int result = BthGetMode(out val);
				if(result!=0)
				{
					throw new System.ComponentModel.Win32Exception(result, "Error getting BluetoothRadio mode");
				}
				return val;
#else            
                return BluetoothRadio.PrimaryRadio.Mode;
#endif

            }
            set
            {
#if (PocketPC)
				int result = BthSetMode(value);
				if(result!=0)
				{
					throw new System.ComponentModel.Win32Exception(result, "Error setting BluetoothRadio mode");
				}
#else
                BluetoothRadio.PrimaryRadio.Mode = value;
#endif

            }
        }


        /// <summary>
        /// Initialize the status of the Bluetooth stack to connectable
        /// </summary>
        /// <returns>True if connected, otherwise false</returns>
        public override bool Initialize()
        {
            try
            {     
                this.Mode = RadioMode.Connectable;
            }
            catch
            {
                return false;
            }
            return true;
        }


        /// <summary>
        /// Open a serial connection to a remote device
        /// </summary>
        /// <param name="buffer">A handle to a circular receive buffer</param>
        /// <param name="sbuffer">A handle to a circular send buffer</param>
        /// <param name="address">A machine independent address of the remote bluetooth device</param>
        /// <param name="pin">A pin for the remote bluetooth device</param>
        /// <returns>A bluetooth stream on success, otherwise null</returns>
        public override BluetoothStream Connect(CircularBuffer buffer,CircularBuffer sbuffer,byte[] address, string pin)
        {
            try
            {
                lock (this)
                {
                    return MicrosoftBluetoothStream.Open(buffer,sbuffer, address, pin);
                }                               
            }
            catch (Exception)
            {
                return null;
            }            
        }

        /// <summary>
        /// Shuts down the bluetooth stack
        /// </summary>
        public override bool Dispose()
        {
            try
            {
                this.Mode = RadioMode.PowerOff;
                return true;
            }
            catch
            {
                return false;
            }
        }
 
        /// <summary>
        /// Not implemented at the moement
        /// </summary>
        /// <returns></returns>
        public override Hashtable Search()
        {
            return null;
        }
      


    }
}
