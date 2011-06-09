using System;
using System.Collections.Generic;
using System.Text;
using System.Collections;

namespace SXML
{
    public class SensorAnnotation
    {
        private string dataset;
        private ArrayList receivers;
        private ArrayList sensors;

        private bool hasBuiltIn;
        //private int num_sensors1;
        //private int num_sensors2;
        private int[] num_sensors;
        private int totalReceivers;
        private bool isHR;
        private int firstAccelerometerID;
        private int maximumSensorID;
        private Hashtable sensorsIndex;
        private int totalBuiltInSensors;
        private int totalBluetoothReceivers;
        private int totalWiredRecerivers;

        public SensorAnnotation(int maxReceivers)
        {
            this.sensors = new ArrayList();
            this.receivers = new ArrayList();
            this.totalBuiltInSensors = 0;
            this.hasBuiltIn = false;
            this.sensorsIndex = new Hashtable();
            //this.num_sensors1 = 0;
            //this.num_sensors2 = 0;
            this.isHR = false;
            this.num_sensors = new int[maxReceivers];
            this.totalReceivers=0;
            this.firstAccelerometerID = -1;
            this.maximumSensorID = -1;
            this.totalBluetoothReceivers = 0;
            this.totalWiredRecerivers = 0;
        }

        public int GetSensor(int receiverID)
        {
            foreach (Sensor sensor in this.sensors)
            {
                if (receiverID == Convert.ToInt32(sensor.Receiver))
                    return Convert.ToInt32(sensor.ID);
            }

            return -1;
        }
        public Hashtable SensorsIndex
        {
            get
            {
                return this.sensorsIndex;
            }
        }
        public int MaximumSensorID
        {
            get
            {
                return this.maximumSensorID;
            }
            set
            {
                this.maximumSensorID = value;
            }
        }
        public int FirstAccelerometer
        {
            get
            {
                return this.firstAccelerometerID;
            }
            set
            {
                this.firstAccelerometerID = value;
            }
        }
        public bool IsHR
        {
            get
            {
                return this.isHR;
            }
            set
            {
                this.isHR = value;
            }
        }

        public string Dataset{
            get{
                return this.dataset;
            }
            set
            {
                this.dataset = value;
            }
        }

        public ArrayList Sensors
        {
            get
            {
                return this.sensors;
            }
        }

        public ArrayList Receivers
        {
            get
            {
                return this.receivers;
            }
        }

        public int TotalBuiltInSensors
        {
            get
            {
                return this.totalBuiltInSensors ;
            }
            set
            {
                this.totalBuiltInSensors = value;
            }
        }

        public bool HasBuiltinSensors
        {
            get
            {
                return this.hasBuiltIn;
            }
            set
            {
                this.hasBuiltIn = value;
            }
        }
        public int TotalReceivers
        {
            get
            {
                return this.totalReceivers;
            }
            set
            {
                this.totalReceivers = value;
            }
        }


        public int TotalBluetoothReceivers
        {
            get
            {
                return this.totalBluetoothReceivers;
            }
            set
            {
                this.totalBluetoothReceivers = value;
            }
        }

        public int TotalWiredReceivers
        {
            get
            {
                return this.totalWiredRecerivers;
            }
            set
            {
                this.totalWiredRecerivers = value;
            }
        }
        public int[] NumberSensors
        {
            get
            {
                return this.num_sensors;
            }
        }

        public int GetNumberSensors(int receiver_id)
        {
            if ((receiver_id < this.num_sensors.Length) && (receiver_id >= 0))
                return this.num_sensors[receiver_id];
            else
                return -1;

        }

        public string toXML()
        {
            string xml = "<"+Constants.SENSORDATA_ELEMENT+" "+
                Constants.DATASET_ATTRIBUTE+"=\""+this.dataset+"\" xmlns=\"urn:mites-schema\">\n";
            foreach (Sensor sensor in this.sensors)            
                xml += sensor.toXML();
            xml += "</" + Constants.SENSORDATA_ELEMENT + ">\n";

            return xml;
        }
     
    }
}
