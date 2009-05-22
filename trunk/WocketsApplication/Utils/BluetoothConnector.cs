using System;
using System.Collections.Generic;
using System.Text;
using System.Threading;
using Wockets.Receivers;
using Wockets;
using System.IO;

namespace WocketsApplication.Utils
{
    public class BluetoothConnector
    {


        private Receiver receiver;
        private WocketsController wocketController;
        private Thread reconnectionThread=null;


        public BluetoothConnector(Receiver receiver,WocketsController wocketController)
        {
            this.wocketController = wocketController;
            this.receiver = receiver;

        }

        public void Cleanup()
        {
            if (reconnectionThread != null)
                reconnectionThread.Abort();
            reconnectionThread = null;
        }

        private void ReconnectThread()
        {
            while((receiver._Type == ReceiverTypes.RFCOMM) && (receiver._Running==false))
            {
                Thread.Sleep(500);
                //this.bluetoothControllers[receiver._ID] = new BluetoothController();
                try
                {
                    receiver.Initialize();
                    //this.bluetoothControllers[receiver._ID].initialize(((RFCOMMReceiver)receiver)._AddressBytes, ((RFCOMMReceiver)receiver)._PIN);
                }
                catch (Exception)
                {
                    return;
                }

                receiver._Running=true;
              
            }
            Cleanup();
        }

        public void Reconnect()
        {

            //if (reconnectionThread != null)
              //  reconnectionThread.Abort();
            if (reconnectionThread == null)
            {
                reconnectionThread = new Thread(new ThreadStart(this.ReconnectThread));
                reconnectionThread.Start();                
            }
        }
    }
}
