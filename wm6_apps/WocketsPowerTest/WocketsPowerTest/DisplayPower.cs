using System;
using System.Runtime.InteropServices;


/// <summary>
/// By Peter Foot, OpenNetCF (originally called Video)
/// http://community.opennetcf.com/forums/t/774.aspx
/// </summary>
public class DisplayPower
{

    // GDI Escapes for ExtEscape()	
    private const uint QUERYESCSUPPORT = 8;
    // The following are unique to CE	
    private const uint GETVFRAMEPHYSICAL = 6144;
    private const uint GETVFRAMELEN = 6145;
    private const uint DBGDRIVERSTAT = 6146;
    private const uint SETPOWERMANAGEMENT = 6147;
    private const uint GETPOWERMANAGEMENT = 6148;

    public static void PowerOff()
    {
        IntPtr hdc = GetDC(IntPtr.Zero);
        //uint func = SETPOWERMANAGEMENT;
        uint size = 12;
        byte[] vpm = new byte[size];
        //structure size		
        BitConverter.GetBytes(size).CopyTo(vpm, 0);
        //dpms version		
        BitConverter.GetBytes(0x0001).CopyTo(vpm, 4);
        //power state		
        BitConverter.GetBytes((uint)VideoPowerState.VideoPowerOff).CopyTo(vpm, 8);
        ExtEscapeSet(hdc, SETPOWERMANAGEMENT, size, vpm, 0, IntPtr.Zero);
    }

    public static void PowerOn()
    {
        IntPtr hdc = GetDC(IntPtr.Zero);
        uint size = 12;
        byte[] vpm = new byte[size];
        //structure size		
        BitConverter.GetBytes(size).CopyTo(vpm, 0);
        //dpms version		
        BitConverter.GetBytes(0x0001).CopyTo(vpm, 4);
        //power state		
        BitConverter.GetBytes((uint)VideoPowerState.VideoPowerOn).CopyTo(vpm, 8);
        ExtEscapeSet(hdc, SETPOWERMANAGEMENT, size, vpm, 0, IntPtr.Zero);
    }

    [DllImport("coredll", EntryPoint = "ExtEscape")]
    private static extern int ExtEscapeSet(IntPtr hdc, uint nEscape, uint cbInput, byte[] lpszInData, int cbOutput, IntPtr lpszOutData);

    [DllImport("coredll")]
    private static extern IntPtr GetDC(IntPtr hwnd);
}

public enum VideoPowerState : uint
{
    VideoPowerOn = 1,
    VideoPowerStandBy,
    VideoPowerSuspend,
    VideoPowerOff
}
    

