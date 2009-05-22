
//
// Win32APIs.cs
//    
//    Implementation of a library to use Win32 Memory Mapped
//    Files from within .NET applications
//
//    Modified to work with .NET Compact Framework (hopefully) --claytonw
//
// COPYRIGHT (C) 2001, Tomas Restrepo (tomasr@mvps.org)
//
// This library is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public
// License as published by the Free Software Foundation; either
// version 2.1 of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public
// License along with this library; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
//

using System;
using System.IO;
using System.Runtime.InteropServices;

namespace Winterdom.IO.FileMap
{

   /// <summary>Win32 APIs used by the library</summary>
   /// <remarks>
   ///   Defines the PInvoke functions we use
   ///   to access the FileMapping Win32 APIs
   /// </remarks>
   internal class Win32MapApis
   {
       private static IntPtr INVALID_HANDLE_VALUE = new IntPtr(-1);//from the Windows APIs

       public static IntPtr CreateFile(String lpFileName, int dwDesiredAccess,
           int dwShareMode, IntPtr lpSecurityAttributes, int dwCreationDisposition,
           int dwFlagsAndAttributes, IntPtr hTemplateFile)
       {
           if (Environment.OSVersion.Platform == PlatformID.Win32Windows)
               return Win32CreateFile(lpFileName, dwDesiredAccess, dwShareMode, lpSecurityAttributes, dwCreationDisposition, dwFlagsAndAttributes, hTemplateFile);
           else
               return WinCECreateFile(lpFileName, dwDesiredAccess, dwShareMode, lpSecurityAttributes, dwCreationDisposition, dwFlagsAndAttributes, hTemplateFile);
       }

       public static IntPtr CreateFileMapping(IntPtr hFile, IntPtr lpAttributes, int flProtect,
          int dwMaximumSizeHigh, int dwMaximumSizeLow, String lpName)
       {
           if (Environment.OSVersion.Platform == PlatformID.Win32Windows)
               return Win32CreateFileMapping(hFile, lpAttributes, flProtect, dwMaximumSizeHigh, dwMaximumSizeLow, lpName);
           else
               return WinCECreateFileMapping(hFile, lpAttributes, flProtect, dwMaximumSizeHigh, dwMaximumSizeLow, lpName);
       }

       public static bool FlushViewOfFile(
           IntPtr lpBaseAddress, int dwNumBytesToFlush)
       {
           if (Environment.OSVersion.Platform == PlatformID.Win32Windows)
               return Win32FlushViewOfFile(lpBaseAddress, dwNumBytesToFlush);
           else
               return WinCEFlushViewOfFile(lpBaseAddress, dwNumBytesToFlush);

       }

       public static IntPtr MapViewOfFile(
           IntPtr hFileMappingObject, int dwDesiredAccess, int dwFileOffsetHigh,
           int dwFileOffsetLow, int dwNumBytesToMap)
       {
           if (Environment.OSVersion.Platform == PlatformID.Win32Windows)
               return Win32MapViewOfFile(hFileMappingObject, dwDesiredAccess, dwFileOffsetHigh, dwFileOffsetLow, dwNumBytesToMap);
           else
               return WinCEMapViewOfFile(hFileMappingObject, dwDesiredAccess, dwFileOffsetHigh, dwFileOffsetLow, dwNumBytesToMap);
       }

       public static IntPtr OpenFileMapping(
         int dwDesiredAccess, bool bInheritHandle, String lpName)
       {
           if (Environment.OSVersion.Platform == PlatformID.Win32Windows)
               return Win32OpenFileMapping(dwDesiredAccess, bInheritHandle, lpName);
           else
           {
               //return WinCEOpenFileMapping(dwDesiredAccess, bInheritHandle, lpName);
               //The OpenFileMapping function isn't exported in WinCE.
               //Instead, we use CreateFileMapping with the appropriate flags
               //TODO: should really handle permissions/security somehow.
               // There's no clear mapping between dwDesiredAccess and 
               // lpAttributes or flProtect. 
               return WinCECreateFileMapping(INVALID_HANDLE_VALUE, IntPtr.Zero, 0, 0, 0, lpName);
           }

       }

       public static bool UnmapViewOfFile(IntPtr lpBaseAddress)
       {
           if (Environment.OSVersion.Platform == PlatformID.Win32Windows)
               return Win32UnmapViewOfFile(lpBaseAddress);
           else
               return WinCEUnmapViewOfFile(lpBaseAddress);
       }

       public static bool CloseHandle(IntPtr handle)
       {
           if (Environment.OSVersion.Platform == PlatformID.Win32Windows)
               return Win32CloseHandle(handle);
           else
               return WinCECloseHandle(handle);
       }

       [ DllImport("kernel32", SetLastError=true, CharSet=CharSet.Auto, EntryPoint="CreateFile") ]
       private static extern IntPtr Win32CreateFile ( 
           String lpFileName, int dwDesiredAccess, int dwShareMode,
           IntPtr lpSecurityAttributes, int dwCreationDisposition,
           int dwFlagsAndAttributes, IntPtr hTemplateFile );
       [DllImport("coredll", SetLastError = true, CharSet = CharSet.Auto, EntryPoint = "CreateFile")]
       private static extern IntPtr WinCECreateFile(
           String lpFileName, int dwDesiredAccess, int dwShareMode,
           IntPtr lpSecurityAttributes, int dwCreationDisposition,
           int dwFlagsAndAttributes, IntPtr hTemplateFile);

       [ DllImport("kernel32", SetLastError=true, CharSet=CharSet.Auto, EntryPoint = "CreateFileMapping") ]
       private static extern IntPtr Win32CreateFileMapping ( 
           IntPtr hFile, IntPtr lpAttributes, int flProtect,
           int dwMaximumSizeHigh, int dwMaximumSizeLow, 
           String lpName );
       [DllImport("coredll", SetLastError=true, CharSet=CharSet.Auto, EntryPoint = "CreateFileMapping")]
       private static extern IntPtr WinCECreateFileMapping(
           IntPtr hFile, IntPtr lpAttributes, int flProtect,
           int dwMaximumSizeHigh, int dwMaximumSizeLow, 
           String lpName);

       [ DllImport("kernel32", SetLastError=true, EntryPoint = "FlushViewOfFile") ]
       private static extern bool Win32FlushViewOfFile ( 
           IntPtr lpBaseAddress, int dwNumBytesToFlush );
       [DllImport("coredll", SetLastError=true, EntryPoint = "FlushViewOfFile")]
       private static extern bool WinCEFlushViewOfFile(
           IntPtr lpBaseAddress, int dwNumBytesToFlush);


       [ DllImport("kernel32", SetLastError=true, EntryPoint = "MapViewOfFile") ]
       private static extern IntPtr Win32MapViewOfFile (
           IntPtr hFileMappingObject, int dwDesiredAccess, int dwFileOffsetHigh,
           int dwFileOffsetLow, int dwNumBytesToMap );
       [DllImport("coredll", SetLastError=true, EntryPoint = "MapViewOfFile")]
       private static extern IntPtr WinCEMapViewOfFile(
           IntPtr hFileMappingObject, int dwDesiredAccess, int dwFileOffsetHigh,
           int dwFileOffsetLow, int dwNumBytesToMap);

       [ DllImport("kernel32", SetLastError=true, CharSet=CharSet.Auto, EntryPoint = "OpenFileMapping") ]
       private static extern IntPtr Win32OpenFileMapping (
           int dwDesiredAccess, bool bInheritHandle, String lpName );
       /*[DllImport("coredll", SetLastError=true, CharSet=CharSet.Auto, EntryPoint = "OpenFileMapping")]
       private static extern IntPtr WinCEOpenFileMapping(
           int dwDesiredAccess, bool bInheritHandle, String lpName);
       */
       [ DllImport("kernel32", SetLastError=true, EntryPoint = "UnmapViewOfFile")]
       private static extern bool Win32UnmapViewOfFile ( IntPtr lpBaseAddress );
       [DllImport("coredll", SetLastError = true, EntryPoint = "UnmapViewOfFile")]
       private static extern bool WinCEUnmapViewOfFile(IntPtr lpBaseAddress);

       [ DllImport("kernel32", SetLastError=true, EntryPoint = "CloseHandle") ]
       private static extern bool Win32CloseHandle ( IntPtr handle );
       [DllImport("coredll", SetLastError = true, EntryPoint = "CloseHandle")]
       private static extern bool WinCECloseHandle(IntPtr handle);

   } // class Win32MapApis

} // namespace Winterdom.IO.FileMap
