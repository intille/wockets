using System;
using System.Collections.Generic;
using System.Text;
using System.Runtime.InteropServices;//Marshall

namespace AppUpdater.Logging
{
    public class SystemStatus
    {
        public static int GetBatteryChargeRemaining()
        {
            int percent = -1;
            try
            {
                PowerStatus.SYSTEM_POWER_STATUS_EX status = new PowerStatus.SYSTEM_POWER_STATUS_EX();
                if (PowerStatus.GetSystemPowerStatusEx(status, false) == 1)
                    percent = status.BatteryLifePercent;

            }
            catch { }

            return percent;

        }
        public static string StatusColumns
        {
            get
            {
                return "Available,Total,AC,Battery %,Backup %,Battery mV,Charging,Battery temp";
            }
        }
        public static int GetAvailablePhysicalMemory()
        {
            MemoryStatus.MEMORYSTATUS memStatus = new MemoryStatus.MEMORYSTATUS();
            MemoryStatus.GlobalMemoryStatus(memStatus);

            return Convert.ToInt32(memStatus.dwAvailPhys);
        }
        public static int GetAvailableVirtualMemory()
        {
            MemoryStatus.MEMORYSTATUS memStatus = new MemoryStatus.MEMORYSTATUS();
            MemoryStatus.GlobalMemoryStatus(memStatus);

            return Convert.ToInt32(memStatus.dwAvailVirtual);
        }
        public static string GetStatusString()
        {
            //available memory, total memory,
            //AC Line status, Battery %, Backup battery %
            //Battery voltage, Battery charging, Battery temperature

            string systemstatus = ",";
            try
            {


                MemoryStatus.MEMORYSTATUS memStatus = new MemoryStatus.MEMORYSTATUS();
                MemoryStatus.GlobalMemoryStatus(memStatus);

                systemstatus += memStatus.dwAvailPhys.ToString() + ",";
                systemstatus += memStatus.dwTotalPhys.ToString() + ",";


                PowerStatus.SYSTEM_POWER_STATUS_EX status = new PowerStatus.SYSTEM_POWER_STATUS_EX();
                PowerStatus.SYSTEM_POWER_STATUS_EX2 status2 = new PowerStatus.SYSTEM_POWER_STATUS_EX2();

                if (PowerStatus.GetSystemPowerStatusEx(status, false) == 1)
                {
                    switch (status.ACLineStatus)
                    {
                        case PowerStatus.AC_LINE_OFFLINE:
                            systemstatus += "Off,";
                            break;
                        case PowerStatus.AC_LINE_ONLINE:
                            systemstatus += "On,";
                            break;
                        case PowerStatus.AC_LINE_BACKUP_POWER:
                            systemstatus += "backup,";
                            break;
                        default:
                            systemstatus += "unknown,";
                            break;
                    }

                    systemstatus += status.BatteryLifePercent.ToString() + ",";
                    systemstatus += status.BackupBatteryLifePercent.ToString() + ",";
                }
                else
                {
                    systemstatus += "FAILURE: GetSystemPowerStatusEx failed,,,";
                }

                if (PowerStatus.GetSystemPowerStatusEx2(status2, (uint)Marshal.SizeOf(status2), false) == (uint)Marshal.SizeOf(status2))
                {

                    systemstatus += status2.BatteryVoltage.ToString() + ",";
                    systemstatus += status2.BatteryFlag.ToString() + ",";
                    systemstatus += status2.BatteryTemperature.ToString();
                }
                else
                {
                    systemstatus += "FAILURE: GetSystemPowerStatusEx2 failed,,";
                }


            }
            catch
            {
            }

            return systemstatus;

        }
    }
}
