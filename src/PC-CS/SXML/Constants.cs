using System;
using System.Collections.Generic;
using System.Text;

namespace SXML
{
    public class Constants
    {
        public const string SENSORDATA_ELEMENT = "SENSORDATA";
        public const string SENSOR_ELEMENT = "SENSOR";
        public const string ID_ELEMENT = "ID";
        public const string OBJECT_ELEMENT = "OBJECT";
        public const string LOCATION_ELEMENT = "LOCATION";
        public const string DESCRIPTION_ELEMENT = "DESCRIPTION";
        public const string DISPLAY_ELEMENT = "DISPLAY";
        public const string COLOR_ELEMENT = "COLOR";
        public const string CALIBRATION_ELEMENT = "CALIBRATION";
        public const string RECEIVER_ELEMENT = "RECEIVER";
        public const string RECEIVERS_ELEMENT = "RECEIVERS";
        public const string SENSORS_ELEMENT = "SENSORS";

        public const string CONFIGURATIONS_ELEMENT = "CONFIGURATIONS";
        public const string SENSORSET_ELEMENT = "SENSORSET";
        public const string NAME_ELEMENT = "NAME";
        public const string FILE_ELEMENT = "FILE";

        //attributes

        public const string DATASET_ATTRIBUTE = "dataset";
        public const string CLASS_ATTRIBUTE = "class";
        public const string TYPE_ATTRIBUTE = "type";
        public const string ID_ATTRIBUTE = "id";
        public const string TEXT_ATTRIBUTE = "text";
        public const string SR_ATTRIBUTE = "sr";
        public const string ON_ATTRIBUTE = "on";
        public const string OFF_ATTRIBUTE = "off";
        public const string XMEAN_ATTRIBUTE = "xmean";
        public const string XSTD_ATTRIBUTE = "xstd";
        public const string YMEAN_ATTRIBUTE = "ymean";
        public const string YSTD_ATTRIBUTE = "ystd";
        public const string ZMEAN_ATTRIBUTE = "zmean";
        public const string ZSTD_ATTRIBUTE = "zstd";
        public const string DISPLAY_TYPE_ATTRIBUTE = "displaytype";
        public const string DISPLAY_X = "x";
        public const string DISPLAY_Y = "y";
        public const string MAC_ATTRIBUTE = "mac";
        public const string PASSKEY_ATTRIBUTE = "passkey";
        public const string DECODER_ATTRIBUTE = "decoder";

        //Sensor Classes
        public const string MITES = "MITes";
        public const string BUILTIN = "BUILTIN";
        public const string WOCKETS = "Wockets";

        //receiver types
        public const string RECEIVER_USB = "usb";
        public const string RECEIVER_BLUETOOTH = "bluetooth";

        //types of decoders
        public const string DECODER_MITES = "mites";
        public const string DECODER_WOCKETS = "wockets";
        public const string DECODER_SPARKFUN= "sparkfun";

        public static int MAC_SIZE = 6;

        

    }
}
