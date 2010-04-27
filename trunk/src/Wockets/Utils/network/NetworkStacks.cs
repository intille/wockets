using System;
using System.Collections.Generic;
using System.Text;
using Wockets;
using Wockets.Utils;
using Wockets.Utils.network.Bluetooth;
using Wockets.Utils.network.Bluetooth.Microsoft;
using Wockets.Utils.network.Bluetooth.Widcomm;
using Wockets.Data.Configuration;


namespace Wockets.Utils.network
{

    /// <summary>
    /// The class provides transparent and unified access to the Bluetooth stack supported on the platform whether it is
    /// Microsoft or Widcomm
    /// </summary>
    public static class NetworkStacks
    {
        /// <summary>
        /// A handle to the bluetooth stack
        /// </summary>
        private static BluetoothStack bluetoothStack = null;

        /// <summary>
        /// A property that returns a handle to the bluetooth stack
        /// </summary>
        public static BluetoothStack _BluetoothStack
        {
            get
            {
                // Intialize the bluetooth stack if necessary
                if (bluetoothStack == null)
                {
                    if (BluetoothStack._Type == BluetoothStackTypes.Microsoft)
                        bluetoothStack = new MicrosoftBluetoothStack();
                    else if (BluetoothStack._Type == BluetoothStackTypes.Widcomm)
                        bluetoothStack = new WidcommBluetoothStack();
                    /*if (!bluetoothStack.Initialize())
                    {
                        Logger.Error("NetworkStacks: _BluetoothStack: Failed to initialize the bluetooth stack");
                        throw new Exception("Bluetooth stack failed to initialize.");                                              
                    }*/
                }
                return bluetoothStack;
            }
            set
            {
                if (value == null)
                {
                    try
                    {
                        bluetoothStack.Dispose();
                        bluetoothStack = null;
                    }
                    catch (Exception e)
                    {
                        bluetoothStack = null; 
                    }
                }
            }
        }
    }
}
