# region using directives
using System;

// serial port references
using System.IO.Ports;

//using System.Runtime.InteropServices;
using System.Net.Sockets;

// 32.feet.NET references
using InTheHand.Net;
using InTheHand.Net.Sockets;
using InTheHand.Net.Bluetooth;
using System.Threading;

using System.Windows.Forms;

#endregion

using Wockets.Decoders.Accelerometers;
using Wockets.Data.Accelerometers;
using Wockets.Utils;

namespace WocketConfigurationApp 
{

	
	public class BtWocketPC
	{

        
	// Bluetooth 
		private BluetoothAddress blt_address = null;
		private BluetoothEndPoint blt_endPoint = null;
        private BluetoothClient bc = null;
        private BluetoothDeviceInfo[] bdi;

        private int WOCKET = 0;
        private int SERIAL_LILYPAD = 1;
        private int BT_TYPE = -1;

        private string bt_type_name = "";

    // Wocket
        private WocketsDecoder wocket_dc;
        //private AccelerationData data; 
        //private AccelerationData prevdata;
        private double lastUnixTime = 0;
           
     //Buffer
        private NetworkStream ns;
		
        private byte[] buffer;
        CircularBuffer cbuffer;
        
        private int received = 0;
		private int MAX_BYTES; 
        

    //Update variable
		private string _LastValue = "";
        private string value = "";

    //Thread
        private object _objLock = new object();
        private Thread readingThread = null;

    //Delegate
        public event OnNewReadingEventHandler OnNewReading;
        public delegate void OnNewReadingEventHandler(object sender, EventArgs e);

     // Reading Flag
        private bool isReading = false;
        private bool address_set = false;
     
    // status
        private string status = "";
        private int behavior  = 0;

    // write alive package to wockets
        public class ALIVE
        {
            protected byte[] cmd;
           

            public byte[] _Bytes
            {
                get
                {
                    return this.cmd;
                }
            }

            

            public ALIVE()
            {
                this.cmd = new byte[] { (byte)0xbb };
               
            }
        }

        private ALIVE Alive_CMD = new ALIVE();
        private int alive_time_offset = 20;
        private int alive = 20;
        
        




//===============================================
        // Initialize 
        // TODO SSI I had to add a "void" to get this to compile
		public void BtSerial(string address,string type_name)

		{
                // check that it doesn't affect the other connections            
                TurnON_BT_Radio();

                Thread.Sleep(50);

                bt_type_name = type_name;

                if (type_name.CompareTo("wocket") == 0)
                {
                    BT_TYPE = WOCKET;
                    MAX_BYTES = 4096;
                    
                    wocket_dc = new WocketsDecoder();
                    Wockets.Utils.WocketsTimer.InitializeTime();
                    cbuffer = new CircularBuffer(MAX_BYTES);
                }
                else if (type_name.CompareTo("lilypad") == 0)
                {
                    BT_TYPE = SERIAL_LILYPAD;
                    MAX_BYTES = 4096;
                }

                //Initialize buffer
                buffer = new byte[MAX_BYTES];
               

                address_set = SetAddress(address);
                   
		}


//===============================================
//sets the address

        public bool SetAddress(string address)
        {
            try
            {
                //Set BT Device Address
                blt_address = BluetoothAddress.Parse(address);

                //Set BT Device Pin
                BluetoothSecurity.SetPin((BluetoothAddress)blt_address, "1234");


                // Create a connection channel specifying the Bluetooth-Serial end-points 
                blt_endPoint = new BluetoothEndPoint((BluetoothAddress)blt_address, BluetoothService.SerialPort);

                
                return true;
            }
            catch
            {
                return false;
            }
        }


        public bool SetAddress(BluetoothAddress address)
        {
            try
            {
                //Set BT Device Address
                blt_address = address;

                //Set BT Device Pin
                BluetoothSecurity.SetPin((BluetoothAddress)blt_address, "1234");

                // Create a connection channel specifying the Bluetooth-Serial end-points 
                blt_endPoint = new BluetoothEndPoint((BluetoothAddress)blt_address, BluetoothService.SerialPort);

                
                return true;
            }
            catch 
            {
                return false;
            }
        }


//========================================================
// controls the connection

        // starts the connection
        // if check_radio == 1 the radio will be checked 
		public bool Start(int check_radio)
		{
            try
            {   

                // make sure radio is on
                if(check_radio == 1)
                    TurnON_BT_Radio();

                // clean up bluetooth if it was open
                if (bc != null)
                {
                    bc.Close();
                    bc.Dispose();
                }

                bc = new BluetoothClient();

                if (bc != null)
                {
                    // check the bt end point
                    if (blt_endPoint == null)
                        blt_endPoint = new BluetoothEndPoint((BluetoothAddress)blt_address, BluetoothService.SerialPort);

                    // check the intialization of the stream
                    if (ns != null)
                    {
                        ns.Close();
                        ns.Dispose();
                    }

                    

                    return true;
                   
                }

                return false;
            }
            catch(Exception e)
            {
                status = e.ToString();
                return false;
            }

		}



        // stops the connection
		public void Stop()
		{
            StopReading();
            CloseConnection();

            // Not turn off radio if handeling multiple connections
            //TurnOFF_BT_Radio();
  
		}


        // restart the connection
        public bool ReStartConnection()
        {
            try
            {
                if (Start(0))
                    return true;
                else
                    return false;
                
            }
            catch
            {
                return false;
            }
        }

//=====================================================
// controls bt radio        
        
        // turn off the radio
        public bool TurnOFF_BT_Radio()
        {
            try
            {
                if ( BluetoothRadio.PrimaryRadio.Mode != RadioMode.PowerOff )
                BluetoothRadio.PrimaryRadio.Mode = RadioMode.PowerOff;

                return true;
            }
            catch
            {
                return false;
            }
        }

        // trun on the radio
        public bool TurnON_BT_Radio()
        {
            try
            {
                if (BluetoothRadio.PrimaryRadio.Mode != RadioMode.Connectable)
                {
                    BluetoothRadio.PrimaryRadio.Mode = RadioMode.PowerOff;
                    BluetoothRadio.PrimaryRadio.Mode = RadioMode.Connectable;
                }
                return true;
            }
            catch(Exception e)
            {
                status = e.ToString();
                return false;
            }
        }


//==================================================================================
// open/close connection

        // open the connection
		public bool OpenConnection()
		{
			// try to connect
			try
			{
                bc.Connect(blt_endPoint);
                return true;
	            
			}
			catch(Exception e)
			{
                status = e.ToString();
				return false;
			}

		}


        // close the connection
		public void CloseConnection()
		{
			if (bc != null)
			{
				bc.Close();
				bc.Dispose();
			}

            if (ns != null)
            {
                ns.Close();
                ns.Dispose();
            }

            blt_endPoint = null;
		}



//===============================================
// Write/Read functionality

        // write the alive package to wocket
        public bool WriteAlive() 
        {
            try
            {
                
                alive = alive - 1;
                if (alive <= 0)
                {
                    // get stream??
                    ns.Write(Alive_CMD._Bytes,0,1);
                    alive = alive_time_offset;
                    return true;
                }

                return false;
            }
            catch(Exception e)
            {
                status = e.ToString();
                return false;
            }

        }

        public bool ReadData(out string out_value)
        {
            bool is_data_available = false;
            out_value = "---";


            try
            {
                // this is necessary
                ns = bc.GetStream();

                if (ns.DataAvailable)
                {
                    
                   received = ns.Read(buffer, 0, MAX_BYTES);
                   

                    if(received >0)
                    {
                        is_data_available = true;

                        if( BT_TYPE == SERIAL_LILYPAD)
                            serial_decoder(buffer, received, out out_value, out behavior);
                        else if(BT_TYPE == WOCKET)
                            wockets_decoder(buffer, received, out out_value, out behavior);
                    }
                    
                }
                else
                {

                    for (int i = 0; i < 3; i++)
                    {
                        System.Threading.Thread.Sleep(500);
                        
                        //this is necessary
                        ns = bc.GetStream();

                        if (ns.DataAvailable)
                        {   
                            received = ns.Read(buffer, 0, MAX_BYTES);
                            
                            if (received > 0)
                            {
                                is_data_available = true;

                                if (BT_TYPE == SERIAL_LILYPAD)
                                    serial_decoder(buffer, received, out out_value, out behavior);
                                else if (BT_TYPE == WOCKET)
                                    wockets_decoder(buffer, received, out out_value, out behavior);

                                break;
                            }
                            else
                            {
                                out_value = "---";
                            }

                        }
                    }
                }//ends else

                return is_data_available;

            }
            catch(Exception e)
            {
                //"Problem reading the data stream"
                status = e.ToString();
                return false;
            }
        }


       
//=================================================
// Decoding Functions

        private int NUM_BUTTONS = 3;
        private int BUTTON_THRESHOLD = 1;
        private int[] button_counter = new int[3];
        private int[] button_activation = new int[3];


        private void serial_decoder(byte[] buffer, int received_bytes,out string output, out int result_behavior)
        {
            byte val = 0;
            int total_activations = 0;
            char[] buf = new char[4];
            string buf_str = "";
            int buf_int = 0;
            output = "";
            
            
            int id = -1;

            // initialize button values
            for (int i = 0; i < NUM_BUTTONS; i++)
            {
                button_counter[i] = 0;
                button_activation[i] = 0;
            }

           
            //sets all data available  
            for (int k = 0; k < received_bytes; k++)
            {
                val = buffer[k];

                //if end of package detected
                if (val == 10)
                {
                    //decode button id
                    id = (int)buffer[k + 1];
                    
                    //check id validity
                    if ((id >0) && (id <= NUM_BUTTONS))
                    {
                        //correct for id arrays start in 0
                        id = id - 1;

                        //decode button value
                        buf[0] = (char)buffer[k + 2];
                        buf[1] = (char)buffer[k + 3];
                        buf[2] = (char)buffer[k + 4];
                        buf[3] = (char)buffer[k + 5];

                        buf_str = buf[0].ToString() + buf[1].ToString() + buf[2].ToString() + buf[3].ToString();
                        Int32.TryParse(buf_str, out buf_int);
                        k = k + 5;

                        //check if value corresponds to button activated
                        if (buf_int == 0)
                        { button_counter[id]++; }
                        //else
                        //{ button_counter[id] = 0; }

                        //if a sequense of button activations is present,
                        //add a button activation to the count
                        //and reset counter
                        if (button_counter[id] > 0)
                        {
                            button_activation[id]++;
                            button_counter[id] = 0;
                        }
                    }
               }
            }//ends for

            //write the buttons activatios found in this read
            buf_str = "";
            for (int j = 0; j < NUM_BUTTONS; j++)
            {
                id=j+1;
                buf_str = buf_str +
                         id.ToString()+ " : " + button_activation[j].ToString() + "\r\n";
                total_activations = total_activations + button_activation[j];
            }

            if (total_activations > BUTTON_THRESHOLD)
            {
                output = output + "active" + "\r\n";
                result_behavior = 1;
            }
            else
            {   output = output + "inactive" + "\r\n";
                result_behavior = 0;
            }

            output = output + buf_str;
        }

//==================================================================
        int lastTail = 0;
        int VMAG_THERSHOLD = 40;

        double[] means = new double[3];
        double[] Rmeans = new double[3];
        int prev = -1;
        double VMAG = 0.0;

        private void wockets_decoder(byte[] buffer, int received_bytes, out string output, out int result_behavior)
        {
            
            
            int ii;
            string status_str;
            output = "";

            //get the position of the last byte written
            int mytail = this.cbuffer._Tail;

            //write the incomming bytes to the circular buffer
            for (ii = 0; ii < received_bytes; ii++)
            {
                // this.buffer._Timestamp[this.buffer._Tail] = timestamp;
                this.cbuffer._Bytes[mytail++] = buffer[ii];
                mytail %= this.cbuffer._Bytes.Length;
            }

            //update the head and tail of buffer
            //this.cbuffer._Head = this.cbuffer._Tail;
            this.cbuffer._Tail = mytail;

            int head = this.cbuffer._Head;
            int tail = this.cbuffer._Tail;
           
            //decode the data for the new bytes
            this.wocket_dc.Decode(0, this.cbuffer, head ,tail);
            this.cbuffer._Head = tail;

            #region commented
            //get the decoded data from new bytes
            //data = ((AccelerationData)this.wocket_dc._Data[tail]);

            //output = "X: " + data.X.ToString() + ", " +
            //         "Y: " + data.Y.ToString() + ", " +
            //         "Z: " + data.Z.ToString() + "\r\n";
            #endregion 

            int DecodedPackets = get_wockets_decoded_data( this.wocket_dc._Head);

           
            /*output = received_bytes.ToString() +","+
                      DecodedPackets.ToString()+ ","+
                      head.ToString() +","+
                      tail.ToString()+ "\r\n";
            */

            status_str = "X: " + ((int)Rmeans[0]).ToString() + "\r\n" +
                        "Y: " + ((int)Rmeans[1]).ToString() + "\r\n" +
                        "Z: " + ((int)Rmeans[2]).ToString() + "\r\n" +
                        "VMAG: " + ((int)VMAG).ToString();

            if (VMAG > VMAG_THERSHOLD)
            {
                output = output + "active" + "\r\n";
                result_behavior = 1;
            }
            else
            {
                output = output + "inactive" + "\r\n";
                result_behavior = 0;
            }

            output = output + status_str;
 

        }


        
       

        

        private int get_wockets_decoded_data(int currentHead)
        {
            
            double tailUnixTimestamp = 0;
            double aUnixTime = 0;
            int DecodedPackets = 0;

            AccelerationData prevdata;
            AccelerationData data = ((AccelerationData)this.wocket_dc._Data[lastTail]);

            //initialize statistics
            int i=0;
            VMAG = 0.0;
            for (i = 0; i < 3; i++)
            {  means[i] = 0;
            
            }


            while ((lastTail != currentHead) && (data.UnixTimeStamp > 0))
            {

                //check that data is valid
                aUnixTime = data.UnixTimeStamp;

               if (aUnixTime < lastUnixTime)
                {
                    status = "Data overwritten without decoding";
                    //Logger.Error(s);
                    break;
                }

                #region commented
                /*
                //else if ((aUnixTime - lastUnixTime) > 2000)
                //    Console.WriteLine("");

                // Roughly once per second save full timestamp, no matter what
                if (isForceTimestampSave || (timeSaveCount == TIMESTAMP_AFTER_SAMPLES))
                {
                    WriteTimeDiff(aUnixTime, lastUnixTime, true); // Force save
                    timeSaveCount = 0;
                }
                else
                {
                    WriteTimeDiff(aUnixTime, lastUnixTime, false);
                    timeSaveCount++;
                }
                 isForceTimestampSave = false;
                

                // Save Raw Bytes                        
                if (bw != null)
                    for (int j = 0; j < data.NumRawBytes; j++)
                        bw.WriteByte(data.RawBytes[j]);
                */

                #endregion


                lastUnixTime = aUnixTime;
                tailUnixTimestamp = aUnixTime;
                
                //if valid, get values for buffer
                means[0] = means[0] + data._X;
                means[1] = means[1] + data._Y;
                means[2] = means[2] + data._Z;

                //make updates of decoded data
                prevdata = data;

                if (lastTail >= this.wocket_dc._Data.Length - 1)
                    lastTail= 0;
                else
                    lastTail++;

                //get new value
                DecodedPackets++;
                data = ((AccelerationData)this.wocket_dc._Data[lastTail]);

                if (prev > -1)
                {
                    VMAG= VMAG + System.Math.Sqrt(System.Math.Pow((double)(data._X - Rmeans[0]), 2.0) +
                                           System.Math.Pow((double)(data._Y - Rmeans[1]), 2.0) +
                                           System.Math.Pow((double)(data._Z - Rmeans[2]), 2.0));           
                }


            }

            //compute the final mean result
            if (DecodedPackets > 1)
            {
                for (i = 0; i < 3; i++)
                { Rmeans[i] = means[i] / DecodedPackets; 
                }

                VMAG = VMAG / DecodedPackets;

                if(prev == -1)
                    prev = 0;
            }


            return DecodedPackets;
        }



//=================================================
        public void StartReading()
        {
            lock (_objLock)
            {
                if (readingThread != null)
                    return;

                readingThread = new Thread(new ThreadStart(ReadingLoop));
                readingThread.Start();
            }
        }


        private void ReadingLoop()
        {

            isReading = true;
            bool isconnected = false;
            bool iscreated = false;
            int trial = 0;


            //Start
            Start(1);


            try
            {
                while (isReading)
                {
                    //OpenConnection 
                    isconnected = OpenConnection();

                    if (isconnected)
                    { iscreated = true; trial = 0; }
                    else
                    { iscreated = false; trial++; }


                    // read loop
                    while (isconnected & isReading)
                    {
                        //Read Data 
                        isconnected = ReadData(out value);
                        _LastValue = value;

                        if (BT_TYPE == WOCKET)
                        { if( WriteAlive())
                            _LastValue = "writing to wocket"; 
                        }

                        
                        //OnNewReading.Invoke(this, null);
                        if (OnNewReading != null)
                            OnNewReading(this, EventArgs.Empty);

                    }


                    // search loop
                    if ((!isconnected) & isReading & (!iscreated))
                    {
                        // Restart connection 
                        // search for device, till it is found it
                        // check if I could use a listener
                        // check SP, check BTC, check radio

                        iscreated = ReStartConnection();


                    }

                    // !!!I am testing this part!!!
                    // If device cannot connect. Try restarting the BT radio
                    if ((!isconnected) & isReading & (iscreated) & (trial >= 10))
                    {
                        Stop();

                        System.Threading.Thread.Sleep(15000);

                        Start(1);
                        trial = 0;

                    }

                }// isReading loop ends


                //If reading loop ends, close Connection 
                CloseConnection();

            }
            catch (Exception e)
            {
                //reading loop has stopped
                status = e.ToString();
            }

        }


        public void StopReading()
        {
            lock (_objLock)
            {
                if (readingThread == null)
                    return;

                isReading = false;
                readingThread.Join();
                readingThread = null;
            }
        }
	


//===================================================
// Retrieve BT data

        //Get the last value read
        public string LastValue
        {
            get
            {
                return _LastValue;
            }
        }

        public int GetBehavior()
        {  
            return behavior;    
        }


        public void SetBehavior(int value)
        {
            lock (_objLock)
            {
                behavior = value;
            }
        }

        public bool IsAddressSet()
        {
            //lock (_objLock)
            //{
            
                return address_set;
           // }
        }



//===================================================
// Status Variables        
        
        // check the status of the bt connection 
        public bool IsConnected()
        {
            return ((BluetoothRadio.PrimaryRadio.Mode != RadioMode.PowerOff) &&
                    (bc.Connected != false) &&
                    (blt_endPoint != null));
        }

        // check the status of the bt connection 
        public bool IsStarted()
        {
            return ((BluetoothRadio.PrimaryRadio.Mode != RadioMode.PowerOff) &&
                    (bc.Connected != false) &&
                    (blt_endPoint != null));
        }


//====================================================
// Bt search function. It is generic for all bts


        public bool Search()
        {
            bool isfound = false;

            // set flags about which devices we want to find
            // the discovery flags are: authenticated, remembered and unknown
            bdi = bc.DiscoverDevices(60, false, true, true);

            if (bdi.Length > 0)
            {
                isfound = true;
            }

            return isfound;

        }

        public BluetoothDeviceInfo[] GetDevicesFound()
        {
            return (bdi);

        }
 //================================================



    } //ends class
}// ends namespace