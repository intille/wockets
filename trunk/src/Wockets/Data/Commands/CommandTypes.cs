using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data
{
    public enum CommandTypes : byte
    {

        /// <summary>
        /// Instruct the radio to enter command mode. 
        /// </summary>
        ENTER_CMD_MODE,
        /// <summary>
        /// Instruct the radio to exit command mode. 
        /// </summary>
        EXIT_CMD_MODE,
        /// <summary>
        /// Instruct the radio to get sniff mode. 
        /// </summary>
        SET_SNIFF_MODE,
        /// <summary>
        /// Instruct the Radio to set sniff mode. 
        /// </summary>
        GET_SNIFF_MODE,
        /// <summary>
        /// Instruct the radio to reset itself. 
        /// </summary>
        RESET,


        SET_LED,               
        GET_BT,
        GET_PC,
        GET_SM,
        SET_SM,
        BT_RST,
        GET_SEN,






        GET_SENSITIVITY,
        SET_SENSITIVITY,
        GET_CALIBRATION,
        SET_CALIBRATION,
        GET_TRANSMISSION_POWER,
        SET_TRANSMISSION_POWER,
        GET_SAMPLING_RATE,
        SET_SAMPLING_RATE,
        GET_DSC,
        SET_DSC,
        GET_TRANSMISSION_MODE,
        SET_TRANSMISSION_MODE,
        GET_ALIVE_TIME,
        SET_ALIVE_TIME,
        GET_POWERDOWN_TIME,
        SET_POWERDOWN_TIME,
        RST_WK,
        GET_CONFIGURATION_TIME,
        SET_CONFIGURATION_TIME,
        GET_BAUD_RATE,
        SET_BAUD_RATE,
        ALIVE,
        GET_BATTERY, 
        RESET_WOCKET

    }
}
