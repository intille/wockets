using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data
{
    public enum CommandTypes : byte
    {
        GET_BT=0,
        GET_BP=1,
        GET_PC=2,
        RST_BT=3,
        GET_SEN=4,
        SET_SEN=5,
        GET_CAL=6,
        SET_CAL=7,
        GET_SR=8,
        SET_SR=9,
        GET_ALT=10,
        SET_ALT=11,
        GET_PDT=12,
        SET_PDT=13,
        RST_WKT=14,
        ALIVE=15,
        PAUSE=16,
        RESUME=17,
        GET_TM=18,
        SET_TM=19,
        GET_BTCAL=20,
        SET_BTCAL=21,
        GET_HV=22,
        GET_FV=23,
        GET_TCT=24,
        SET_TCT=25,
        SET_VTM = 26,
        ACK=27
    }
}
