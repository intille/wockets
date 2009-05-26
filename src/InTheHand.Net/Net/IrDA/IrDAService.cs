// 32feet.NET - Personal Area Networking for .NET
//
// InTheHand.Net.IrDA.IrDAService
// 
// Copyright (c) 2003-2006 In The Hand Ltd, All rights reserved.
// This source code is licensed under the In The Hand Community License - see License.txt

#region Using directives

using System;

#endregion

namespace InTheHand.Net.IrDA
{
    /// <summary>
    /// Standard IrDA service names.
    /// </summary>
#if V2
    public static class IrDAService
    {
#else
    public class IrDAService
    {
        private IrDAService(){}
#endif

        /// <summary>
        /// Well-known Service Name &#x201C;IrDA:IrCOMM&#x201D;
        /// </summary>
        public const string IrComm = "IrDA:IrCOMM";
        /// <summary>
        /// Well-known Service Name &#x201C;IrLPT&#x201D;
        /// </summary>
        public const string IrLpt = "IrLPT";
        /// <summary>
        /// Well-known Service Name &#x201C;OBEX&#x201D;
        /// </summary>
        public const string ObjectExchange = "OBEX";

    }
}
