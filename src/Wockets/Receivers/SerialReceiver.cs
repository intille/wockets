using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Receivers
{
    public abstract class SerialReceiver:Receiver
    {
        #region Serialization Constants
        protected const string PARITY_ATTRIBUTE = "Parity";
        protected const string STOPBIT_ATTRIBUTE = "StopBit";
        protected const string BAUD_RATE_ATTRIBUTE = "BaudRate";
        protected const string PORT_NUMBER_ATTRIBUTE = "PortNumber";
        #endregion Serialization Constants

        private int portNumber;
        private int baudRate;
        private bool useParity;
        private bool useStopbit;

        public SerialReceiver(int bufferSize):base(bufferSize)
        {            
        }
        /*
        public SerialReceiver(int bufferSize,int portNumber,int baudRate,bool useParity,bool useStopbit,int max_sr):base(bufferSize,max_sr)
        {
            this.portNumber = portNumber;
            this.baudRate = baudRate;
            this.useParity = useParity;
            this.useStopbit = useStopbit;
        }
        */
        #region Access Properties
        public int _PortNumber
        {
            get
            {
                return this.portNumber;
            }
            set
            {
                this.portNumber = value;
            }

        }

        public int _BaudRate
        {
            get
            {
                return this.baudRate;
            }

            set
            {
                this.baudRate = value;
            }
        }

        public bool _Parity
        {
            get
            {
                return this.useParity;
            }

            set
            {
                this.useParity = value;
            }
        }

        public bool _StopBit
        {
            get
            {
                return this.useStopbit;
            }

            set
            {
                this.useStopbit = value;
            }
        }
        #endregion Access Properties

        public override int CompareTo(object receiver)
        {
            return this._PortNumber.CompareTo(((SerialReceiver)receiver)._PortNumber);
        }
     
    }
}
