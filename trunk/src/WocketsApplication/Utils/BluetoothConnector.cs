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
        private bool reconnecting = false;




        public BluetoothConnector(Receiver receiver,WocketsController wocketController)
        {
            this.wocketController = wocketController;
            this.receiver = receiver;

        }

        public bool Reconnecting
        {
            get
            {
                return this.reconnecting;
            }
        }
        public void Cleanup()
        {            
            if (reconnectionThread != null)
                reconnectionThread.Abort();
            reconnectionThread = null;
            reconnecting = false;
        }

        private void ReconnectThread()
        {
            while((receiver._Type == ReceiverTypes.RFCOMM) && (receiver._Running==false))
            {               
                try
                {
                    receiver.Initialize();                    
                    receiver._Running = true;                                        
                }
                catch (Exception e)
                {
                    Thread.Sleep(500);
                }                
              
            }
            Cleanup();
            
        }

        public void Reconnect()
        {
            if (reconnectionThread == null)
            {
                reconnecting = true;
                Thread.Sleep(1000);
                reconnectionThread = new Thread(new ThreadStart(this.ReconnectThread));
                //reconnectionThread.Priority = ThreadPriority.Highest;
                reconnectionThread.Start();                
            }
        }
    }
}
