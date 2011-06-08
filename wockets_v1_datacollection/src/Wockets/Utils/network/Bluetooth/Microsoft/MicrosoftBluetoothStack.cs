using System;
using System.Collections.Generic;
using System.Text;
using System.Collections;
using System.Runtime.InteropServices;
using Wockets.Utils.network.Bluetooth;

namespace Wockets.Utils.network.Bluetooth.Microsoft
{
    public class MicrosoftBluetoothStack : BluetoothStack
    {

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

        public RadioMode Mode
        {
            get
            {

                RadioMode val;
                int result = BthGetMode(out val);
                if (result != 0)
                {
                    throw new System.ComponentModel.Win32Exception(result, "Error getting BluetoothRadio mode");
                }
                return val;

            }
            set
            {

                int result = BthSetMode(value);
                if (result != 0)
                {
                    throw new System.ComponentModel.Win32Exception(result, "Error setting BluetoothRadio mode");
                }

            }
        }


        public MicrosoftBluetoothStack()
        {
            this.Mode = RadioMode.PowerOff;
            this.Mode = RadioMode.Connectable;
        }


        public override bool Initialize()
        {
            this.Mode = RadioMode.Connectable;
            return true;
        }


        public override BluetoothStream Connect(CircularBuffer buffer, CircularBuffer sbuffer, byte[] address, string pin)
        {
            try
            {
                lock (this)
                {
                    return MicrosoftBluetoothStream.Open(buffer, sbuffer, address, pin);
                }
            }
            catch (Exception e)
            {
                return null;
            }
        }

        public override BluetoothStatus _Status
        {
            get
            {

                if (this.Mode == RadioMode.Connectable)
                    this.status = BluetoothStatus.Up;
                else if (this.Mode == RadioMode.PowerOff)
                    this.status = BluetoothStatus.Down;
                else
                    this.status = BluetoothStatus.Error;

                return this.status;
            }
        }
        public override Hashtable Search()
        {
            return null;
        }
        public override void Dispose()
        {
            this.Mode = RadioMode.PowerOff;
        }


    }
}
