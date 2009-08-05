using System;
using System.Collections.Generic;
using System.Text;
using System.Collections;
using InTheHand.Net.Bluetooth;
using Wockets.Utils.network.Bluetooth;

namespace Wockets.Utils.network.Bluetooth.Microsoft
{
    public class MicrosoftBluetoothStack : BluetoothStack
    {

        public MicrosoftBluetoothStack()
        {
            BluetoothRadio.PrimaryRadio.Mode = RadioMode.PowerOff;
            BluetoothRadio.PrimaryRadio.Mode = RadioMode.Connectable;
        }

        public override bool Initialize()
        {
            BluetoothRadio.PrimaryRadio.Mode = RadioMode.Connectable;
            return true;
        }

        public override BluetoothStream Connect(byte[] buffer,byte[] address, string pin)
        {
            try
            {
                //cleanup any resources if a previous connection existed
                //this.Disconnect(address);
                MicrosoftBluetoothStream btStream = new MicrosoftBluetoothStream(buffer,address,pin);
                if (btStream.Open())
                {
                    this.bluetoothStreams.Add(btStream);
                    return btStream;
                }
                else                    
                    return null;
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
                
                if (BluetoothRadio.PrimaryRadio.Mode == RadioMode.Connectable)
                    this.status = BluetoothStatus.Up;
                else if (BluetoothRadio.PrimaryRadio.Mode == RadioMode.PowerOff)
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
            BluetoothRadio.PrimaryRadio.Mode = RadioMode.PowerOff;
        }


    }
}
