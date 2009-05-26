// 32feet.NET - Personal Area Networking for .NET
//
// InTheHand.Net.Utilities
// 
// Copyright (c) 2003-2007 In The Hand Ltd, All rights reserved.
// This source code is licensed under the In The Hand Community License - see License.txt

using System;
using System.Runtime.InteropServices;

namespace InTheHand.Net
{
    internal sealed class PlatformVerification
    {
        private PlatformVerification() { }

        public static void ThrowException()
        {
#if WinCE
            if (System.Environment.OSVersion.Platform != PlatformID.WinCE)
            {
                throw new PlatformNotSupportedException("This .NET Compact Framework version of the 32feet.NET assembly can not be run on the desktop .NET framework");
            }
#endif
		}
    }

    // <summary>
    // Helper class for GCHandle.
    // </summary>
    internal sealed class GCHandleHelper
    {
#if WinCE && V1
        private static bool v1 = false;

        static GCHandleHelper()
        {
            string s = "Marshal";
            GCHandle h = GCHandle.Alloc(s.ToCharArray(), GCHandleType.Pinned);
            IntPtr p = h.AddrOfPinnedObject();
            short c1 = Marshal.ReadInt16(p);
            if (c1 != 0x4d)
            {
                v1 = true;
            }
            else
            {
                v1 = false;
            }

            h.Free();
        }
#endif

        private GCHandleHelper() { }

        // <summary>
        // Returns the memory address of the pinned item.
        // </summary>
        // <param name="handle">GCHandle allocated as Pinned.</param>
        // <returns>Address of the pinned item.</returns>
        public static IntPtr AddrOfPinnedObject(GCHandle handle)
        {
#if WinCE && V1
            if (v1 && handle.Target.GetType().IsClass)
            {
                return new IntPtr(handle.AddrOfPinnedObject().ToInt32() + 4);
            }
            else
            {
                return handle.AddrOfPinnedObject();
            }
#else
            //on CF2 or desktop use the standard API method
            return handle.AddrOfPinnedObject();
#endif

        }

    }

    //--------------------------------------------------------------------------
    internal
#if ! V1
    static
#endif
    class ExceptionFactory
    {
#if V1
        private ExceptionFactory() { }
#endif

        /// <exclude/>
        [System.ComponentModel.EditorBrowsable(System.ComponentModel.EditorBrowsableState.Advanced)]
#if CODE_ANALYSIS
        [System.Diagnostics.CodeAnalysis.SuppressMessage("Microsoft.Naming", "CA1704:IdentifiersShouldBeSpelledCorrectly", MessageId = "0#param",
            Justification = "Verbatim copy of FX version!")]
#endif
        public static ArgumentOutOfRangeException ArgumentOutOfRangeException(String paramName, String message)
        {
#if V1 //&& NETCF
            return new ArgumentOutOfRangeException(message);
#else
            return new ArgumentOutOfRangeException(paramName, message);
#endif
        }

    }//class


    //--------------------------------------------------------------------------
    internal
#if ! V1
    static
#endif
    class StringUtilities
    {
#if V1
        private StringUtilities() { }
#endif

        /// <exclude/>
        [System.ComponentModel.EditorBrowsable(System.ComponentModel.EditorBrowsableState.Advanced)]
        public static bool IsNullOrEmpty(String value)
        {
#if V1
            if (value == null) return true;
            if (value.Length == 0) return true;
            return false;
#else
            return String.IsNullOrEmpty(value);
#endif
        }

    }//class

}
