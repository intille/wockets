using System;
using System.Collections.Generic;
using System.Text;

namespace WocketsAppNS
{
    public class Constants
    {
        //Screen placement and sizes
        public const int MAX_FORM_WIDTH= 400;
        public const int MAX_FORM_HEIGHT = 300;
        public const int WIDGET_SPACING = 2;
        public const int MIN_FONT = 9;
        public const int MAX_FONT = 64;
        public const string FONT_FAMILY = "Microsoft Sans Serif";
        public static int FORM_MIN_WIDTH = 30;
        public static int FORM_MIN_HEIGHT = 30;


#if (PocketPC)        
        public static string NEEDED_FILES_PATH = "\\Program Files\\wockets\\NeededFiles\\";
#else 
        public static string NEEDED_FILES_PATH = "..\\NeededFiles\\"; //relative to bin
#endif

        public static string MASTER_DIRECTORY = NEEDED_FILES_PATH + "Master\\";
        public static string ACTIVITY_PROTOCOLS_DIRECTORY = NEEDED_FILES_PATH + "ActivityProtocols\\";
        public static string SENSOR_CONFIGURATIONS_DIRECTORY = NEEDED_FILES_PATH + "SensorConfigurations\\";
        public static string CALIBRATIONS_DIRECTORY = NEEDED_FILES_PATH + "images\\calibrations\\";
        public static string NETWORK_STATUS_DIRECTORY = NEEDED_FILES_PATH + "images\\network\\";
    
    }
}
