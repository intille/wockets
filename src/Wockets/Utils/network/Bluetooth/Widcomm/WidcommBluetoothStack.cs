using System;
using System.Collections.Generic;
using System.Text;
using System.Collections;
using System.Runtime.InteropServices;
using Wockets.Utils.network.Bluetooth;

namespace Wockets.Utils.network.Bluetooth.Widcomm
{
    internal class WidcommAPI
    {
        private const string widcommDLL = "WidcommPPC.dll";

        [DllImport(widcommDLL, SetLastError = false, CharSet = CharSet.Unicode)]
        internal static extern IntPtr CreateWidcommStack();

        [DllImport(widcommDLL, SetLastError = false, CharSet = CharSet.Unicode)]
        internal static extern bool SetAutoReconnect(IntPtr wdStack);

        [DllImport(widcommDLL, SetLastError = false, CharSet = CharSet.Unicode)]
        internal static extern bool DeleteWidcommStack(IntPtr wdStack);

        [DllImport(widcommDLL, SetLastError = false, CharSet = CharSet.Unicode)]
        internal static extern bool IsStackServerUp(IntPtr wdStack);

        [DllImport(widcommDLL, SetLastError = false, CharSet = CharSet.Unicode)]
        internal static extern bool IsDeviceReady(IntPtr wdStack);

        [DllImport(widcommDLL, SetLastError = false, CharSet = CharSet.Unicode)]
        internal static extern int GetStackStatus(IntPtr wdStack);

        [DllImport(widcommDLL, SetLastError = false, CharSet = CharSet.Unicode)]
        internal static extern bool StartInquiry(IntPtr wdStack);

        [DllImport(widcommDLL, SetLastError = false, CharSet = CharSet.Unicode)]
        internal static extern void StopInquiry(IntPtr wdStack);

        [DllImport(widcommDLL, SetLastError = false, CharSet = CharSet.Unicode)]
        internal static extern bool InquiryCompleteEvent(IntPtr wdStack, out long device_index);

        [DllImport(widcommDLL, SetLastError = false, CharSet = CharSet.Unicode)]
        internal static extern IntPtr DeviceResponded(IntPtr wdStack, out long l, long device_index);

        [DllImport(widcommDLL, SetLastError = false, CharSet = CharSet.Unicode)]
        internal static extern int SppComPort(IntPtr wdStack);

        [DllImport(widcommDLL, SetLastError = false, CharSet = CharSet.Unicode)]
        internal static extern int Bond(IntPtr wdStack, long pbda,string pin);

        [DllImport(widcommDLL, SetLastError = false, CharSet = CharSet.Unicode)]
        internal static extern int SppCreateConnection(IntPtr wdStack, byte scn, long pbda);

        [DllImport(widcommDLL, SetLastError = false, CharSet = CharSet.Unicode)]
        internal static extern int SppRemoveConnection(IntPtr wdStack);

    }

    public class WidcommBluetoothStack : BluetoothStack
    {
        private IntPtr wdStack= IntPtr.Zero;
        private bool m_bDisposed = false;

        public WidcommBluetoothStack()
        {
        }

        ~WidcommBluetoothStack()
        {
            Dispose();
        }


        public IntPtr _Reference
        {
            get
            {
                return this.wdStack;
            }
            set
            {
                this.wdStack = value;
            }
        }
        public override BluetoothStatus _Status
        {
            get
            {
                int widcomstatus=WidcommAPI.GetStackStatus(this.wdStack);
                if (widcomstatus == 0)
                    return BluetoothStatus.Down;
                else if (widcomstatus == 1)
                    return BluetoothStatus.Up;
                else if (widcomstatus == 3)
                    return BluetoothStatus.Unloaded;
                else
                    return BluetoothStatus.Error;
            }
        }
        public override bool Initialize()
        {           
            //create Widcomm stack object
            this.wdStack = WidcommAPI.CreateWidcommStack();
            //set the stack to auto reconnect = true
            if ((this.wdStack != null) && (WidcommAPI.SetAutoReconnect(this.wdStack)))
                return true;
            else
                return false;

        }

        public override BluetoothStream Connect(CircularBuffer buffer,CircularBuffer sbuffer, byte[] address, string pin)
        {
            try
            {
                WidcommBluetoothStream bluetoothStream = new WidcommBluetoothStream(buffer,sbuffer, address, pin);
                if (bluetoothStream.Open())
                {
                    //this.bluetoothStreams.Add(bluetoothStream);
                    return bluetoothStream;
                }
            }
            catch (Exception e)
            {
            }
          
                
            return null;
        }

        public override Hashtable Search()
        {
            Hashtable bt_devices = new Hashtable();
            bt_devices.Clear();
            long device_index = 0;

            //start inquiry
            WidcommAPI.StartInquiry(this.wdStack);

            //bt_devices[0] = "Inq. Result: " + SensorLib.Widcomm.StartInquiry(Widcomm.wdStack).ToString();
            //bt_devices[1] = "Stack Status: " + SensorLib.Widcomm.GetStackStatus(Widcomm.wdStack).ToString();

            DateTime dt_start = DateTime.Now;

            //InquiryCompleteEvent returns the NEXT free device_index

            while (!WidcommAPI.InquiryCompleteEvent(this.wdStack, out device_index) && DateTime.Now < dt_start.AddSeconds(20))
            {
                System.Windows.Forms.Application.DoEvents();
            }

            //bt_devices[0] = "Found:" + device_index.ToString();

            for (int i = 0; i < device_index; i++)
            {
                long vl = 0;
                System.IntPtr l = WidcommAPI.DeviceResponded(this.wdStack, out vl, i);
                bt_devices[vl] = Marshal.PtrToStringUni(l);
            }

            return bt_devices;
        }

        public override void Dispose()
        {
            if (m_bDisposed)
                return;

            if (this.wdStack != IntPtr.Zero)
                WidcommAPI.DeleteWidcommStack(this.wdStack);
            this.wdStack = IntPtr.Zero;

            m_bDisposed = true;
            GC.SuppressFinalize(this);
        }


        public int OpenSPP(long bt_address)
        {
            int comPort = 0;

            WidcommAPI.SppCreateConnection(this.wdStack, 0, bt_address);

            int retry = 0;
            while (retry < 5)
            {
                System.Threading.Thread.Sleep(500);
                comPort = WidcommAPI.SppComPort(this.wdStack);
                retry++;
            }

            return comPort;
        }

        public int CloseSPP()
        {
            int result = WidcommAPI.SppRemoveConnection(this.wdStack);
            return result;
        }





    }
}
