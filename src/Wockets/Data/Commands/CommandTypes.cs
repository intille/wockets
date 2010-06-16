using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data
{
    public enum CommandTypes : byte
    {
        GET_BT,
        GET_BP,
        GET_PC,
        RST_BT,
        GET_SEN,
        SET_SEN,
        GET_CAL,
        SET_CAL,
        GET_SR,
        SET_SR,
        GET_ALT,
        SET_ALT,
        GET_PDT,
        SET_PDT,
        RST_WKT,
        ALIVE,
        PAUSE,
        RESUME,
        GET_TM,
        SET_TM
    }
}
