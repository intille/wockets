using System;
using System.Collections.Generic;
using System.Runtime.InteropServices;
using System.Text;
using System.Xml;
#if (PocketPC)
using Microsoft.WindowsMobile.Status;
#endif
using Wockets.Data;
using Wockets.Utils;
using System.Threading;
using Microsoft.Win32; 

namespace Wockets.Receivers
{
    #region HTC Diamond Objects
    public enum ScreenOrientation
    {
        Landscape = 0,
        ReverseLandscape = 1,
        Portrait = 2,
        ReversePortrait = 3, // upside down
        FaceDown = 4,
        FaceUp = 5
    }

    public struct GVector
    {
        public GVector(double x, double y, double z)
        {
            myX = x;
            myY = y;
            myZ = z;
        }
        double myX;

        public double X
        {
            get { return myX; }
            set { myX = value; }
        }
        double myY;

        public double Y
        {
            get { return myY; }
            set { myY = value; }
        }
        double myZ;

        public double Z
        {
            get { return myZ; }
            set { myZ = value; }
        }

        public GVector Normalize()
        {
            return Scale(1 / Length);
        }

        public GVector Scale(double scale)
        {
            GVector ret = this;
            ret.myX *= scale;
            ret.myY *= scale;
            ret.myZ *= scale;
            return ret;
        }

        public double Length
        {
            get
            {
                return Math.Sqrt(myX * myX + myY * myY + myZ * myZ);
            }
        }

        public override string ToString()
        {
            return string.Format("X={0} Y={1} Z={2}", Math.Round(myX, 4), Math.Round(myY, 4), Math.Round(myZ, 4));
        }
    }

    public delegate void OrientationChangedHandler(IGSensor sender);
    public interface IGSensor
    {
#if (PocketPC)
        ScreenOrientation Orientation
        {
            get;
        }

        event OrientationChangedHandler OrientationChanged;
#endif
    }

    struct HTCGSensorData
    {
        public short TiltX;          // From -1000 to 1000 (about), 0 is flat
        public short TiltY;          // From -1000 to 1000 (about), 0 is flat
        public short TiltZ;          // From -1000 to 1000 (about), 0 = Straight up, -1000 = Flat, 1000 = Upside down
        public short Unknown1;       // Always zero
        public int AngleY;         // From 0 to 359
        public int AngleX;         // From 0 to 359
        public int Unknown2;       // Bit field?
    };

    #endregion  HTC Diamond Objects

    public class HTCDiamondReceiver : Receiver , IGSensor
    {

        #region Serialization Constants
        private const string HTC_TYPE = "HTCDiamond";
        #endregion Serialization Constants

        private const int MAXIMUM_SAMPLING_RATE = 20;
        private const int BUFFER_SIZE = 1024;
        private const int SEND_BUFFER_SIZE = 0;
        //private int bufferIndex;
        private double lastTS;
        private int sampleTimeSpace = 0;
        private Thread pollingThread;

#if (PocketPC)

        #region HTC Diamond Touch Code
        enum HTCSensor : uint
        {
            GSensor = 1
        }

        enum HTCSensitivity : uint
        {
            TWOG = 0 //0 and 2
        }
        #region HTCSensorSDK
        // The following PInvokes were ported from the results of the reverse engineering done
        // by Scott at scottandmichelle.net.
        // Blog post: http://scottandmichelle.net/scott/comments.html?entry=784
        [DllImport("HTCSensorSDK")]
        extern static IntPtr HTCSensorOpen(HTCSensor sensor);

        [DllImport("HTCSensorSDK")]
        extern static void HTCSensorClose(IntPtr handle);

        [DllImport("GSensor")]
        extern static void ECS_PowerDown(uint level);

        [DllImport("GSensor")]
        extern static void ECS_PowerUp();

        [DllImport("HTCSensorSDK")]
        extern static IntPtr HTCSensorGetDataOutput(IntPtr handle, out HTCGSensorData sensorData);


        [DllImport("HTCSensorSDK")]
        extern static void HTCSensorSetSensitivity(IntPtr handle, HTCSensitivity sensitivity);        

        [DllImport("HTCSensorSDK")]
        extern static HTCSensitivity HTCSensorGetSensitivity(IntPtr handle);

        [DllImport("HTCSensorSDK")]
        extern static uint HTCSensorSetPollingInterval(IntPtr handle,uint poll);

        [DllImport("HTCSensorSDK")]
        extern static IntPtr HTCSensorGetPollingInterval(IntPtr handle, out uint poll);
        #endregion

        IntPtr myHandle = HTCSensorOpen(HTCSensor.GSensor);



        [DllImport("coredll")]
        extern static bool CloseHandle(IntPtr handle);

        [DllImport("coredll", SetLastError = true)]
        extern static IntPtr CreateEvent(IntPtr eventAttributes, bool manualReset, bool intialState, string name);

        [DllImport("coredll", SetLastError = true)]
        extern static bool EventModify(IntPtr handle, uint func);
        //#define SENSOR_START        _T("HTC_GSENSOR_SERVICESTART")
        //#define SENSOR_STOP         _T("HTC_GSENSOR_SERVICESTOP")

        static bool SetEvent(IntPtr handle)
        {
            return EventModify(handle, 3);
        }


        void myOrientationState_Changed(object sender, ChangeEventArgs args)
        {
            if (myOrientationChangedHandler != null)
                myOrientationChangedHandler(this);
        }

        #region ISensor Members

#if (PocketPC)
        RegistryState myOrientationState = new RegistryState(@"HKEY_LOCAL_MACHINE\Software\HTC\HTCSensor\GSensor", "EventChanged");
#endif
        // #define SN_GSENSOR_BITMASK  0xF

        public ScreenOrientation Orientation
        {
            get
            {
                return (ScreenOrientation)((int)myOrientationState.CurrentValue & 0xF);
            }
        }

        OrientationChangedHandler myOrientationChangedHandler;
        public event OrientationChangedHandler OrientationChanged
        {
            add
            {
                myOrientationChangedHandler += value;
            }
            remove
            {
                myOrientationChangedHandler -= value;
            }
        }

        #endregion
        #endregion HTC Diamond Touch Code

#endif
        uint ttt = 9999;
        public HTCDiamondReceiver()
            : base(BUFFER_SIZE)
        {
            //this.bufferIndex = 0;
            this.type = ReceiverTypes.HTCDiamond;
            this.lastTS = WocketsTimer.GetUnixTime();
            this.sampleTimeSpace = 1000 / MAXIMUM_SAMPLING_RATE;
//            HTCSensorSetSensitivity(myHandle, HTCSensitivity.TWOG);
            //HTCSensorSetPollingInterval(myHandle,200);
            //HTCSensorGetPollingInterval(myHandle, out ttt);
            //HTCSensorClose(myHandle);
            //ECS_PowerDown(1);
            //ECS_PowerUp();
            //myHandle=HTCSensorOpen(HTCSensor.GSensor);
            //HTCSensorGetPollingInterval(myHandle, out ttt);
            /*for (uint x = 0; (x < uint.MaxValue); x++)
            {

                ttt = HTCSensorSetPollingInterval(myHandle, x);
                if (ttt == 0)
                    Console.WriteLine();
                Thread.Sleep(10);
            }*/
        }


        private void Poll()
        {
            while (this._Status == ReceiverStatus.Connected)
            {
                Read();
                Thread.Sleep(this.sampleTimeSpace);
            }
        }

 
        public override bool Initialize()
        {
            
#if (PocketPC)

            IntPtr hEvent = CreateEvent(IntPtr.Zero, true, false, "HTC_GSENSOR_SERVICESTART");
            SetEvent(hEvent);
            CloseHandle(hEvent);
            myOrientationState.Changed += new ChangeEventHandler(myOrientationState_Changed);

            RegistryKey rk = Registry.LocalMachine.OpenSubKey("System\\CurrentControlSet\\Control\\Power\\State\\Unattended", true);
            rk.SetValue("ecs1:", 0, RegistryValueKind.DWord);
            rk.Close();

            this.status = ReceiverStatus.Connected;
            this.pollingThread = new Thread(new ThreadStart(Poll));
            this.pollingThread.Priority = ThreadPriority.Highest;
            this.pollingThread.Start();
#endif
            return true;
        }

        int kkk = 0;
        /// <summary>
        /// Returns a vector that desribes the direction of gravity/acceleration in relation to the device screen.
        /// When the device is face up on a flat surface, this method would return 0, 0, -9.8.
        /// The Z value of -9.8 would mean that the acceleration in the opposite direction of the orientation of the screen.
        /// When the device is held up, this method would return 0, -9.8, 0.
        /// The Y value of -9.8 would mean that the device is accelerating in the direction of the bottom of the screen.
        /// Conversely, if the device is held upside down, this method would return 0, 9.8, 0.
        /// </summary>
        /// <returns>
        /// The vector returned will have a length measured in the unit meters per second square.
        /// Ideally the when the device is in a motionless state, the vector would be of length 9.8.
        /// However, the sensor is not extremely accurate, so this almost never the case.
        /// </returns>
        public int Read()
        {
            kkk++;

          /*  if (kkk == 200)
                ECS_PowerUp();
            else if (kkk == 400)
            {
                ECS_PowerDown(1);
                kkk = 0;
            }*/
#if (PocketPC)

            //Check for the 20Hz
            double now = WocketsTimer.GetUnixTime();
            if ((now - lastTS) < this.sampleTimeSpace)
                return 0;
            lastTS = now;


            HTCGSensorData data;
            HTCSensorGetDataOutput(myHandle, out data);

            int mytail = 0;
            mytail = this._Buffer._Tail;

            this._Buffer._Bytes[mytail++] = 0xff;
            mytail = mytail % this._Buffer._Bytes.Length;

            byte[] bytes = BitConverter.GetBytes(data.TiltX);
            for (int i = 0; (i < bytes.Length); i++)
            {
                this._Buffer._Bytes[mytail++] = bytes[i];
                mytail = mytail % this._Buffer._Bytes.Length;
            }

            bytes = BitConverter.GetBytes(data.TiltY);
            for (int i = 0; (i < bytes.Length); i++)
            {
                this._Buffer._Bytes[mytail++] = bytes[i];
                mytail = mytail % this._Buffer._Bytes.Length;
            }

            bytes = BitConverter.GetBytes(data.TiltZ);
            for (int i = 0; (i < bytes.Length); i++)
            {
                this._Buffer._Bytes[mytail++] = bytes[i];
                mytail = mytail % this._Buffer._Bytes.Length;
            }

            bytes = BitConverter.GetBytes(data.AngleX);
            for (int i = 0; (i < bytes.Length); i++)
            {
                this._Buffer._Bytes[mytail++] = bytes[i];
                mytail = mytail % this._Buffer._Bytes.Length;
            }

            bytes = BitConverter.GetBytes(data.AngleY);
            for (int i = 0; (i < bytes.Length); i++)
            {
                this._Buffer._Bytes[mytail++] = bytes[i];
                mytail = mytail % this._Buffer._Bytes.Length;
            }
            this._Buffer._Bytes[mytail++] = 0xff;
            mytail = mytail % this._Buffer._Bytes.Length;

            this._Buffer._Tail = mytail;
#endif
            return BUFFER_SIZE;
        }
        public override void Update()
        {
        }
        public  void Write(byte[] data, int length)
        {
            throw new Exception("HTC Diamond Touch: writing to this data source is not implemented");
        }
        public override bool Dispose()
        {
            #if (PocketPC)

            this._Status = ReceiverStatus.Disconnected;
            if (myHandle != IntPtr.Zero)
            {
                HTCSensorClose(myHandle);
                myHandle = IntPtr.Zero;
            }
            using (myOrientationState)
            {
                myOrientationState.Changed -= new ChangeEventHandler(myOrientationState_Changed);
            }
            myOrientationState = null;
            myOrientationChangedHandler = null;

            // note: I noticed in Scott's code, on the shutdown he fires the "HTC_GSENSOR_SERVICESTART" event again.
            // I am guessing that is a bug in his code.
            // My theory is the service start/stop manage a reference count to the service.
            // Once it hits 0, the service is stopped.
            IntPtr hEvent = CreateEvent(IntPtr.Zero, true, false, "HTC_GSENSOR_SERVICESTOP");
            SetEvent(hEvent);
            CloseHandle(hEvent);  
#endif

            return true;
        }

        #region Serialization Methods
        public override string ToXML()
        {
            string xml = "<" + HTCDiamondReceiver.RECEIVER_ELEMENT + " ";
            xml += HTCDiamondReceiver.ID_ATTRIBUTE + "=\"" + this._ID + "\" ";
            xml += HTCDiamondReceiver.TYPE_ATTRIBUTE + "=\"" + HTCDiamondReceiver.HTC_TYPE + "\" ";
            xml += HTCDiamondReceiver.BUFFERSIZE_ATTRIBUTE + "=\"" + this._Buffer._Bytes.Length + "\" ";
            xml += HTCDiamondReceiver.MAX_SR_ATTRIBUTE + "=\"" + this._MaximumSamplingRate + "\" ";
            xml += "/>";
            return xml;
        }
        public override void FromXML(string xml)
        {
            XmlDocument dom = new XmlDocument();
            dom.LoadXml(xml);
            XmlNode xNode = dom.DocumentElement;

            if ((xNode.Name == StandardCOMReceiver.RECEIVER_ELEMENT))
            {
                foreach (XmlAttribute xAttribute in xNode.Attributes)
                {
                    if ((xAttribute.Name == HTCDiamondReceiver.TYPE_ATTRIBUTE) && (xAttribute.Value != HTCDiamondReceiver.HTC_TYPE))
                        throw new Exception("XML Parsing error - HTCDiamond receiver parsing a receiver of a different type " + xAttribute.Value);
                    else if (xAttribute.Name == HTCDiamondReceiver.BUFFERSIZE_ATTRIBUTE)
                        this._Buffer = new CircularBuffer(Convert.ToInt32(xAttribute.Value));//new byte[Convert.ToInt32(xAttribute.Value)];
                    else if (xAttribute.Name == HTCDiamondReceiver.MAX_SR_ATTRIBUTE)
                        this._MaximumSamplingRate = Convert.ToInt32(xAttribute.Value);
                    else if (xAttribute.Name == HTCDiamondReceiver.ID_ATTRIBUTE)
                        this._ID = Convert.ToInt32(xAttribute.Value);

                }
            }
        }


        #endregion Serialization Methods

        public override int CompareTo(object receiver)
        {
            return 0;
        }

    }
}
