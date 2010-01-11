/**
 * 
 * File Name:  omxSP_FFTInit_C_SC16.c
 * OpenMAX DL: v1.0.2
 * Revision:   8916
 * Date:       Wednesday, October 31, 2007
 * 
 * (c) Copyright 2007 ARM Limited. All Rights Reserved.
 * 
 * 
 * Description:
 * Initializes the specification structures required
 */

#include "stdafx.h"
#include "omxtypes.h"
#include "armOMX.h"
#include "omxSP.h"
#include "armCOMM.h"
#include "armSP.h"
#include <math.h>  

/**
 * Function: omxSP_FFTInit_C_SC16
 *
 * Description:
 * These functions initialize the specification structures required for the
 * complex FFT and IFFT functions.
 *
 * Remarks:
 * Desired block length is specified as an input. The function is used to
 * initialize the specification structures for functions <FFTFwd_CToC_SC16_Sfs>
 * and <FFTInv_CToC_SC16_Sfs>. Memory for the specification structure *pFFTSpec
 * must be allocated prior to calling this function. The space required for
 * *pFFTSpec, in bytes, can be determined using <FFTGetBufSize_C_SC16>.
 *
 * Parameters:
 * [in]  order       	base-2 logarithm of the desired block length;
 *				valid in the range [0,12].
 * [out] pFFTSpec		pointer to initialized specification structure.
 *
 * Return Value:
 * Standard omxError result. See enumeration for possible result codes.
 *
 */

OMXResult omxSP_FFTInit_C_SC16(
     OMXFFTSpec_C_SC16* pFFTSpec,
     OMX_INT order
 )

 {
    OMX_INT     i;
    OMX_FC64    *pTwiddle, *pBuf;
    OMX_U16     *pBitRev;
    OMX_F64     W;
    OMX_INT     Nby2, N;
    OMX_U32     Val, BitR;
    ARMsFFTSpec_FC64 *pFFTStruct = 0;

    /* Input parameter check */ 
    armRetArgErrIf(pFFTSpec == NULL, OMX_Sts_BadArgErr)
    armRetArgErrIf(armNot4ByteAligned(pFFTSpec), OMX_Sts_BadArgErr)
    armRetArgErrIf(order < 0, OMX_Sts_BadArgErr)
    armRetArgErrIf(order > 12, OMX_Sts_BadArgErr)
    
    pFFTStruct = (ARMsFFTSpec_FC64 *) pFFTSpec;

    /* if order zero no init is needed */
    if (order == 0)
    {
        pFFTStruct->N = 1;
        return OMX_Sts_NoErr;
    }

    /* Do the initializations */
    Nby2 = 1 << (order - 1);
    N = Nby2 << 1;
    
    pBitRev = (OMX_U16 *) 
        (sizeof(ARMsFFTSpec_FC64) + (OMX_S8*) pFFTSpec);
    pTwiddle = (OMX_FC64 *) 
        (sizeof(OMX_U16) * (N/* - 1*/) + (OMX_S8*) pBitRev);
    pBuf = (OMX_FC64 *)        
        (sizeof(OMX_FC64) * (Nby2) + (OMX_S8*) pTwiddle);

    /* Bitreversed Index's */
    BitR = 0;
    pBitRev [0] = 0;
    for (i = 1; i < N; i++)
    {
        for (Val = N >> 1; BitR & Val; Val >>= 1)
        {
            BitR ^= Val;        
        }
        BitR ^= Val;
        pBitRev [i /*- 1*/] = BitR;
    }

    /* 
     * Filling Twiddle factors 
     *
     * W = (-2 * PI) / N 
     * N = 1 << order
     * W = -PI >> (order - 1)
     */
    W = -PI / Nby2;

    pTwiddle [0] . Re = 1; /*(OMX_S32)(1 * (1 << 15));*/
    pTwiddle [0] . Im = 0;
    for (i = 1; i < Nby2; i++)
    {
        /* store twiddle fac in q15 format */
        pTwiddle[i].Re = cos (W * i);
        pTwiddle[i].Im = sin (W * i);
    }


    /* Update the structure */
    pFFTStruct->N = N;
    pFFTStruct->pTwiddle = pTwiddle;
    pFFTStruct->pBitRev = pBitRev;
    pFFTStruct->pBuf = pBuf;

    return OMX_Sts_NoErr;
}

/*****************************************************************************
 *                              END OF FILE
 *****************************************************************************/

