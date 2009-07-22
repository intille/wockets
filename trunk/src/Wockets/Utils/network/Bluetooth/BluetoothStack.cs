using System;
using System.Collections.Generic;
using System.Text;
using System.Collections;
using Microsoft.Win32; 

namespace Wockets.Utils.network.Bluetooth
{
    public abstract class BluetoothStack
    {
        protected BluetoothStatus status;
        private static BluetoothStackTypes type;
        protected BluetoothStreamList bluetoothStreams;

        public BluetoothStack()
        {
            this.status = BluetoothStatus.Down;
            this.bluetoothStreams = new BluetoothStreamList();
        }

        public BluetoothStreamList _Streams
        {
            get
            {
                return this.bluetoothStreams;
            }
            set
            {
                this.bluetoothStreams = value;
            }
        }
        public static BluetoothStackTypes _Type
        {
            get
            {
                //Determine the type of Bluetooth Stack
                RegistryKey rk = Registry.LocalMachine.OpenSubKey("Software\\WIDCOMM\\");
                if (rk != null)
                    type = BluetoothStackTypes.Widcomm;
                else
                {
                    rk = null;
                    rk = Registry.LocalMachine.OpenSubKey("Software\\Microsoft\\Bluetooth\\");
                    if (rk != null)
                        type = BluetoothStackTypes.Microsoft;
                    else
                        type = BluetoothStackTypes.Unknown;
                }
                return type;
            }
        }
        public abstract BluetoothStatus Status
        {
            get;
        }

        public virtual bool Disconnect(byte[] address)
        {
            long disconnectAddress = BitConverter.ToInt64(address,0);
            foreach (BluetoothStream b in this.bluetoothStreams)
                if (BitConverter.ToInt64(b._Address,0) == disconnectAddress)
                {
                    this.bluetoothStreams.Remove(b);
                    b.Close();
                    return true;
                }
            return false;
        }

        public abstract bool Initialize();
        public abstract Hashtable Search();
        public abstract BluetoothStream Connect(byte[] buffer, byte[] address, string pin);
        public abstract void Dispose();
    }
}
