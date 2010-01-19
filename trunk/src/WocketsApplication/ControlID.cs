using System;
using System.Linq;
using System.Collections.Generic;
using System.Text;

namespace WocketsApplication
{
    public class ControlID
    {
        public const int NUMBER_PANELS = 11;
        public const int HOME_PANEL = 0;
        public const int HOME_PANEL_BUTTON_COUNT = 9;
        public const int ABOUT_PANEL = 1;
        public const int ABOUT_PANEL_BUTTON_COUNT = 0;
        public const int SETTINGS_PANEL = 2;
        public const int SETTINGS_PANEL_BUTTON_COUNT = 3;        
        public const int WOCKETS_PANEL = 3;
        public const int WOCKETS_PANEL_BUTTON_COUNT = 4;
        public const int WOCKETS_CONFIGURATION_PANEL = 4;
        public const int WOCKETS_CONFIGURATION_PANEL_BUTTON_COUNT = 6;
        public const int PLOTTER_PANEL = 5;
        public const int PLOTTER_PANEL_BUTTON_COUNT = 1;


        


        

        //Home Screen                
        public const int LINE_CHART_BUTTON = 0;
        public const int ACTIVITY_BUTTON = 1;
        public const int BATTERY_BUTTON = 2;

        public const int GO_GREEN_BUTTON = 3;

        public const int CONNECT_BUTTON = 4;
        public const int KERNEL_BUTTON = 5;

        public const int SETTINGS_BUTTON = 6;
        public const int MINIMIZE_BUTTON = 7;
        public const int RESET_BUTTON = 8;
        
//        public const int DISCONNECT_BUTTON = 4;
  //      public const int RECORD_BUTTON = 10;
        //public const int STOP_KERNEL_BUTTON = 9;





        //public const int ANNOTATE_BUTTON = 1;
        //public const int STATISTICS_BUTTON = 2;      
        //public const int QUALITY_BUTTON = 3;
    




        public const int HEALTH_BUTTON = 11;


        #region ACTIVITY_PANEL
        public const int ACTIVITY_PANEL = 8;
        public const int ACTIVITY_PANEL_BUTTON_COUNT = 3;
        public const int MEASURE_ACTIVITY_BUTTON = 0;
        public const int ANNOTATE_ACTIVITY_BUTTON = 1;
        public const int HOME_ACTIVITY_BUTTON = 2;
        #endregion ACTIVITY_PANEL

        #region ANNOTATION PROTOCOL PANEL
        public const int ANNOTATION_PROTCOLS_PANEL = 6;
        public const int ANNOTATION_PROTOCOLS_PANEL_BUTTON_COUNT = 1;
        public const int HOME_ANNOTATION_PROTOCOL_BUTTON = 0;
        #endregion ANNOTATION PROTOCOL PANEL

        #region ANNOTATION BUTTON PANEL
        public const int ANNOTATION_BUTTON_PANEL = 7;
        public const int ANNOTATION_BUTTON_PANEL_BUTTON_COUNT = 1;
        public const int HOME_ANNOTATION_BUTTON_BUTTON = 0;
        public const int FINISH_ANNOTATION_BUTTON_BUTTON = 1;
        #endregion ANNOTATION BUTTON PANEL


        #region MODELS PANEL
        public const int MODELS_PANEL = 9;
        public const int MODELS_PANEL_BUTTON_COUNT = 1;
        public const int HOME_MODELS_BUTTON = 0;
        #endregion MODELS PANEL


        #region CLASSIFICATION PANEL
        public const int CLASSIFICATION_PANEL = 10;
        public const int CLASSIFICATION_PANEL_BUTTON_COUNT = 1;
        public const int HOME_CLASSIFICATION_BUTTON = 0;
        #endregion CLASSIFICATION PANEL
        //Settings Screen
       
        public const int BLUETOOTH_BUTTON = 0;
        public const int SOUND_BUTTON = 1;
        public const int BACK_BUTTON = 2;

        //Wockets List Screen
       
        public const int WOCKETS_BACK_BUTTON = 0;
        public const int WOCKETS_UP_BUTTON = 1;
        public const int WOCKETS_DOWN_BUTTON = 2;
        //public const int WOCKETS_SAVE_BUTTON = 3;
        public const int WOCKETS_RELOAD_BUTTON = 3;

        //Wockets Detail Screen
        public const int WOCKETS_CONFIGURATIONS_BACK_BUTTON = 0;        
        public const int WOCKETS_CONFIGURATIONS_BLUETOOTH_BUTTON = 1;
        public const int WOCKETS_CONFIGURATIONS_COMMAND_BUTTON = 2;
        public const int WOCKETS_CONFIGURATIONS_TIMERS_BUTTON = 3;
        public const int WOCKETS_CONFIGURATIONS_STATUS_BUTTON = 4;
        public const int WOCKETS_CONFIGURATIONS_INFORMATION_BUTTON = 5;
        public const int WOCKETS_CONFIGURATIONS_UPDATE_BUTTON = 6;

        //Plotter Screen

        public const int PLOTTER_BACK_BUTTON = 0;

        //Annotation Screen

        public const int ANNOTATION_BACK_BUTTON = 0;

        //Annotation Screen

        public const int ANNOTATION_BUTTON_BACK_BUTTON = 0;
    }
}
