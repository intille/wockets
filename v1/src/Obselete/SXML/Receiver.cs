using System;
using System.Collections.Generic;
using System.Text;

namespace SXML
{
    public class Receiver
    {
        public const int STATUS_CONNECTED = 0;
        public const int STATUS_DISCONNECTED = 1;
        public const int STATUS_RESTARTING = 2;
        public const int STATUS_RESTARTED = 3;

        private int id;
        private string mac;
        private string passkey;
        private string type;
        private byte[] macAddress;
        private string decoder;

        private int status;


        public Receiver()
        {
            this.macAddress = new byte[Constants.MAC_SIZE];
            this.status = STATUS_DISCONNECTED;
        }

        public int Status
        {
            get
            {
                return this.status;
            }

            set
            {
                this.status = value;
            }
        }
        public bool isConnected()
        {
            return (this.status == STATUS_CONNECTED);
        }

        public bool isRestarting()
        {
            return (this.status == STATUS_RESTARTING) ; 
        }

        public bool isRestarted()
        {
            return (this.status == STATUS_RESTARTED);
        }

        public bool isDisconnected()
        {
            return (this.status == STATUS_DISCONNECTED);
        }

  
        public int ID
        {
            get
            {
                return this.id;
            }

            set
            {
                this.id = value;
            }
        }
        public string Decoder
        {
            get
            {
                return this.decoder;
            }

            set
            {
                this.decoder = value;
            }
        }

        public string MAC
        {
            get
            {
                return this.mac;
            }

            set
            {
                this.mac = value;
            }
        }

        public byte[] MacAddress
        {
            get
            {
                return this.macAddress;
            }
        }

        public string PassKey
        {
            get
            {
                return this.passkey;
            }

            set
            {
                this.passkey = value;
            }
        }

        public string Type
        {
            get
            {
                return this.type;
            }

            set
            {
                this.type = value;
            }
        }

        public bool isBluetooth()
        {
            if (this.type == Constants.RECEIVER_BLUETOOTH)
                return true;
            else
                return false;
        }

        public bool isUSB()
        {
            if (this.type == Constants.RECEIVER_USB)
                return true;
            else
                return false;
        }
    }
}
