using System;
using System.Collections.Generic;
using System.Text;
using System.Runtime.InteropServices;

namespace WocketsApplication.Controls
{

         public enum FullScreenFlags : int
        {
            SwHide = 0,
            ShowTaskbar = 0x1,
            HideTaskbar = 0x2,
            ShowSipButton = 0x4,
            HideSipButton = 0x8,
            SwRestore = 9,
            ShowStartIcon = 0x10,
            HideStartIcon = 0x20

        }

        public enum ShowWindowFlags : int
        {
            SW_HIDE = 0x00,
            SW_SHOW = 0x0001 
        }

        public struct RECT
        {
            public int left;
            public int top;
            public int right;
            public int bottom;
        }

        public class ScreenUtils
        {
            [DllImport("aygshell.dll", SetLastError = true)]
            extern public static bool SHFullScreen(IntPtr hwnd, int state);

            [DllImport("coredll.dll", SetLastError = true)]
            extern public static IntPtr FindWindowW(string lpClass, string lpWindow);

            [DllImport("coredll.dll", EntryPoint = "GetForegroundWindow", SetLastError = true)]
            extern public static IntPtr GetForegroundWindow();

            [DllImport("coredll.dll", EntryPoint = "EnableWindow")]
            extern public static bool EnableWindow(IntPtr hwnd, bool bEnable);

            [DllImport("coredll.dll", CharSet = CharSet.Auto)]
            extern public static bool ShowWindow(IntPtr hwnd, int nCmdShow);

            [DllImport("coredll.dll", CharSet = CharSet.Auto)]
            internal static extern bool GetWindowRect(IntPtr hWnd, ref RECT rect);

            [DllImport("coredll.dll", CharSet = CharSet.Auto)]
            internal static extern void MoveWindow(IntPtr hwnd, int X, int Y, int nWidth, int nHeight, bool bRepaint);


            public static void ShowTaskBar(bool bShow)
            {
                {
                    IntPtr h = ScreenUtils.FindWindowW("HHTaskBar", "");
                    ScreenUtils.ShowWindow(h, bShow ? (int)ShowWindowFlags.SW_SHOW : (int)ShowWindowFlags.SW_HIDE);
                    ScreenUtils.EnableWindow(h, bShow);
                }
            }

            public static void ShowTrayBar(bool bShow)
            {
                {
                    IntPtr h = ScreenUtils.FindWindowW("Tray",null);
                    ScreenUtils.ShowWindow(h, bShow ? (int)ShowWindowFlags.SW_SHOW : (int)ShowWindowFlags.SW_HIDE);
                    ScreenUtils.EnableWindow(h, bShow);
                }
            }

        }
}
