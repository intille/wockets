using System;
using System.Collections.Generic;
using System.Text;
using System.Runtime.InteropServices;

namespace Wockets.Utils
{
    // http://msdn.microsoft.com/en-us/library/aa926903.aspx
    public enum ACLineStatus : byte
    {
        AC_LINE_OFFLINE = 0, // Offline
        AC_LINE_ONLINE = 1, // Online
        AC_LINE_BACKUP_POWER = 2, // Backup Power
        AC_LINE_UNKNOWN = 0xFF, //
        Unknown = 0xFF, //status
    }

    public enum BatteryFlag : byte
    {
        BATTERY_FLAG_HIGH = 0x01,
        BATTERY_FLAG_CRITICAL = 0x04,
        BATTERY_FLAG_CHARGING = 0x08,
        BATTERY_FLAG_NO_BATTERY = 0x80,
        BATTERY_FLAG_UNKNOWN = 0xFF,
        BATTERY_FLAG_LOW = 0x02
    }

    public enum BatteryChemistry : byte
    {
        BATTERY_CHEMISTRY_ALKALINE = 0x01,  // Alkaline battery.
        BATTERY_CHEMISTRY_NICD = 0x02, // Nickel Cadmium battery.
        BATTERY_CHEMISTRY_NIMH = 0x03, // Nickel Metal Hydride battery.
        BATTERY_CHEMISTRY_LION = 0x04, // Lithium Ion battery.
        BATTERY_CHEMISTRY_LIPOLY = 0x05, // Lithium Polymer battery.
        BATTERY_CHEMISTRY_ZINCAIR = 0x06, // Zinc Air battery.
        BATTERY_CHEMISTRY_UNKNOWN = 0xFF // Battery chemistry is unknown.
    }

    [StructLayout(LayoutKind.Sequential)]
    public class SYSTEM_POWER_STATUS_EX2
    {
        //AC power status.
        public ACLineStatus ACLineStatus;
        //Battery charge status
        public BatteryFlag BatteryFlag;
        // Percentage of full battery charge remaining. Must be in
        // the range 0 to 100, or BATTERY_PERCENTAGE_UNKNOWN if
        // percentage of battery life remaining is unknown
        public byte BatteryLifePercent;
        byte Reserved1;
        //Percentage of full battery charge remaining. Must be
        // in the range 0 to 100, or BATTERY_PERCENTAGE_UNKNOWN
        // if percentage of battery life remaining is unknown.
        public int BatteryLifeTime;
        // Number of seconds of battery life when at full charge,
        // or BATTERY_LIFE_UNKNOWN if full lifetime of battery is unknown
        public int BatteryFullLifeTime;
        byte Reserved2;
        // Backup battery charge status.
        public BatteryFlag BackupBatteryFlag;
        // Percentage of full backup battery charge remaining. Must be in
        // the range 0 to 100, or BATTERY_PERCENTAGE_UNKNOWN if percentage
        // of backup battery life remaining is unknown.

        public byte BackupBatteryLifePercent;
        byte Reserved3;
        // Number of seconds of backup battery life when at full charge, or
        // BATTERY_LIFE_UNKNOWN if number of seconds of backup battery life
        // remaining is unknown.
        public int BackupBatteryLifeTime;
        // Number of seconds of backup battery life when at full charge, or
        // BATTERY_LIFE_UNKNOWN if full lifetime of backup battery is unknown
        public int BackupBatteryFullLifeTime;
        // Number of millivolts (mV) of battery voltage. It can range from 0
        // to 65535
        public int BatteryVoltage;
        // Number of milliamps (mA) of instantaneous current drain. It can
        // range from 0 to 32767 for charge and 0 to –32768 for discharge.
        public int BatteryCurrent;
        //Number of milliseconds (mS) that is the time constant interval
        // used in reporting BatteryAverageCurrent.
        public int BatteryAverageCurrent;
        // Number of milliseconds (mS) that is the time constant interval
        // used in reporting BatteryAverageCurrent.

        public int BatteryAverageInterval;
        // Average number of milliamp hours (mAh) of long-term cumulative
        // average discharge. It can range from 0 to –32768. This value is
        // reset when the batteries are charged or changed.

        public int BatterymAHourConsumed;
        // Battery temperature reported in 0.1 degree Celsius increments. It
        // can range from –3276.8 to 3276.7.
        public int BatteryTemperature;
        // Number of millivolts (mV) of backup battery voltage. It can range
        // from 0 to 65535.
        public int BackupBatteryVoltage;
        // Type of battery.
        public BatteryChemistry BatteryChemistry;
        // Add any extra information after the BatteryChemistry member.
    } 

    public class Battery
    {

        [DllImport("CoreDLL")]
        public static extern int GetSystemPowerStatusEx2(
        SYSTEM_POWER_STATUS_EX2 statusInfo,
        int length,
        int getLatest
        );


        public static SYSTEM_POWER_STATUS_EX2 GetSystemPowerStatus()
        {
            SYSTEM_POWER_STATUS_EX2 retVal = new SYSTEM_POWER_STATUS_EX2();
            int result = GetSystemPowerStatusEx2(retVal, Marshal.SizeOf(retVal), 1);
            return retVal;
        } 
    }
}
