using System.Reflection;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

//
// General Information about an assembly is controlled through the following 
// set of attributes. Change these attribute values to modify the information
// associated with an assembly.
//
[assembly: AssemblyTitle("InTheHand.Net")]
[assembly: AssemblyDescription("Personal Area Networking for .NET\r\n(" +
#if WinXP
 ".NET Framework"
#elif WinCE
 ".NET Compact Framework"
#else
"unknown!"
#error Unknown platform!
#endif
 + " " +
#if V1
"v1.0"
#elif V2
 "v2.0"
#else
"unknown!"
#error Unknown version!
#endif
 + ")")]

[assembly: AssemblyCompany("In The Hand Ltd")]
[assembly: AssemblyProduct("32feet.NET")]
[assembly: AssemblyCopyright("Copyright © In The Hand Ltd 2003-2008")]
[assembly: AssemblyTrademark("")]
[assembly: AssemblyCulture("")]
[assembly: Guid("f8b087d0-bc47-48ca-958c-8fc6a41c1b65")]

//
// Version information for an assembly consists of the following four values:
//
//      Major Version
//      Minor Version 
//      Build Number
//      Revision
//
// You can specify all the values or you can default the Revision and Build Numbers 
// by using the '*' as shown below:

[assembly: AssemblyVersion("2.3.0.0")]
[assembly: AssemblyInformationalVersion("2.3.0530.0")]
[assembly: System.CLSCompliant(true)]

#if WinXP
[assembly: ComVisible(false)]
#endif

[assembly: AssemblyDelaySign(false)]
//only sign on non-debug builds
#if !DEBUG
[assembly: AssemblyKeyFile("C:\\InTheHand.snk")]
#endif
[assembly: AssemblyKeyName("")]