using System;
using System.Collections.Generic;
using System.Text;
using Wockets.Utils.network.Bluetooth;
using System.IO.Ports;

namespace Wockets.Utils.network.Bluetooth.Widcomm
{
    public class WidcommBluetoothStream: BluetoothStream
    {
        private int comPort = 0;
        private SerialPort spp;
        public WidcommBluetoothStream(byte[] buffer, byte[] address, string pin)
            : base(buffer)
        {            
            /*long bt_address = BitConverter.ToInt64(buffer, 0);
            WidcommAPI.SppCreateConnection(this.wdStack, 0, bt_address);
            int retry = 0;
            while (retry < 5)
            {
                System.Threading.Thread.Sleep(500);
                comPort = WidcommAPI.SppComPort(this.wdStack);
                retry++;
            }
            if (comPort > 0)
            {
                spp = new SerialPort("COM"+comPort, 38400, Parity.None, 8, StopBits.One);
                spp = Handshake.None; 
            }*/
        }

        public override bool Open()
        {
            try
            {
                this.spp.Open();
            }
            catch (Exception e)
            {
            }
            return true;
        }
        public override void Process()
        {
            while (this.status == BluetoothStatus.Up)
            {
                int bytesReceived = 0;

                try
                {
                }
                catch (Exception e)
                {
                }
            }
        }
        public override bool Close()
        {
            this.spp.Close();
            return true;
        }
    }
}
