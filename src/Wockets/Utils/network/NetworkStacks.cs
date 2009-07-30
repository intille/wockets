using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Utils.network.Bluetooth;
using Wockets.Utils.network.Bluetooth.Microsoft;
using Wockets.Utils.network.Bluetooth.Widcomm;

namespace Wockets.Utils.network
{
    public static class NetworkStacks
    {
        private static BluetoothStack bluetoothStack = null;

        public static BluetoothStack _BluetoothStack
        {
            get
            {
                if (bluetoothStack == null)
                {
                    if (BluetoothStack._Type == BluetoothStackTypes.Microsoft)
                        bluetoothStack = new MicrosoftBluetoothStack();
                    else if (BluetoothStack._Type == BluetoothStackTypes.Widcomm)
                        bluetoothStack = new WidcommBluetoothStack();
                    if (!bluetoothStack.Initialize())
                        throw new Exception("Bluetooth stack failed to initialize.");
                }
                return bluetoothStack;
            }
        }
    }
}
