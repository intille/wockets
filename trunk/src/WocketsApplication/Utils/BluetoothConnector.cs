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
        private long time_disconnected = 0;
        private long last_disconnection;
        private int numDisconnections = 0;




        public BluetoothConnector(Receiver receiver,WocketsController wocketController)
        {
            this.wocketController = wocketController;
            this.receiver = receiver;

        }

        //Returns total time disconnected in seconds
        public int TimeDisconnected
        {
            get
            {
                return (int)(this.time_disconnected / 10000000);
            }
            set
            {
                this.time_disconnected = (long)(value * 10000000);
            }
        }

        public int Disconnections
        {
            get
            {
                return this.numDisconnections;
            }

            set
            {
                this.numDisconnections = value;
            }
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
                    if (receiver.Initialize())
                    {
                        receiver._Running = true;
                        this.time_disconnected += (DateTime.Now.Ticks - this.last_disconnection);
                        Wockets.Utils.Logger.Warn("Receiver " + receiver._ID + " has reconnected.");
                    }                               
                }
                catch (Exception e)
                {                   
                }
                Thread.Sleep(500);
              
            }
            Cleanup();
            
        }

        public void Reconnect()
        {
            if (reconnectionThread == null)
            {
                this.numDisconnections++;
                this.last_disconnection = DateTime.Now.Ticks;
                reconnecting = true;
                Thread.Sleep(1000);
                reconnectionThread = new Thread(new ThreadStart(this.ReconnectThread));
               // reconnectionThread.Priority = ThreadPriority.Normal;
                reconnectionThread.Start();                
            }
        }
    }
}
