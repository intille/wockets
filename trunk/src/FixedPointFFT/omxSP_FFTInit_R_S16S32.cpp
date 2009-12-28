/**
 * 
 * File Name:  omxSP_FFTInit_R_S16S32.c
 * OpenMAX DL: v1.0.2
 * Revision:   8916
 * Date:       Wednesday, October 31, 2007
 * 
 * (c) Copyright 2007 ARM Limited. All Rights Reserved.
 * 
 * 
 * Description:
 * Initialize the real forward-FFT specification information struct
 */

#include "stdafx.h"
#include "omxtypes.h"
#include "armOMX.h"
#include "omxSP.h"
#include "armCOMM.h"
#include "armSP.h"
#include <math.h>  

/**
 * Function: omxSP_FFTInit_R_S16_S32
 *
 * Description:
 * Initialize the real forward-FFT specification information struct.
 *
 * Remarks:
 * This function is used to initialize the specification structures
 * for functions <ippsFFTFwd_RToCCS_S16_S32_Sfs> and
 * <ippsFFTInv_CCSToR_S32_S16_Sfs>. Memory for *pFFTSpec must be
 * allocated prior to calling this function. The number of bytes
 * required for *pFFTSpec can be determined using
 * <FFTGetBufSize_R_S16_S32>.
 *
 * Parameters:
 * [in]  order       base-2 logarithm of the desired block length;
 *			   valid in the range [0,12].
 * [out] pFFTFwdSpec pointer to the initialized specification structure.
 *
 * Return Value:
 * Standard omxError result. See enumeration for possible result codes.
 *
 */

OMXResult omxSP_FFTInit_R_S16S32(
     OMXFFTSpec_R_S16S32* pFFTSpec,
     OMX_INT order
 )
{
    OMX_INT     i;
    OMX_FC64    *pTwiddle;
    OMX_U16     *pBitRev;
    OMX_F64     *pBuf;
    OMX_F64     W;
    OMX_INT     Nby2;
    OMX_U32     Val, BitR;
    ARMsFFTSpec_R_FC64 *pFFTStruct = 0;

    /* Input parameter check */ 
    armRetArgErrIf(pFFTSpec == NULL, OMX_Sts_BadArgErr)
    armRetArgErrIf(armNot8ByteAligned(pFFTSpec), OMX_Sts_BadArgErr)
    armRetArgErrIf(order < 0, OMX_Sts_BadArgErr)
    armRetArgErrIf(order > 12, OMX_Sts_BadArgErr)
    
    pFFTStruct = (ARMsFFTSpec_R_FC64 *) pFFTSpec;

    /* if order zero no init is needed */
    if (order == 0)
    {
        pFFTStruct->N = 1;
        return OMX_Sts_NoErr;
    }

    /* Do the initializations */
    Nby2 = 1 << (order - 1);
    
    pBitRev = (OMX_U16 *) 
        (sizeof(ARMsFFTSpec_R_FC64) + (OMX_S8*) pFFTSpec);
    pTwiddle = (OMX_FC64 *) 
        (sizeof(OMX_U16) * Nby2 + (OMX_S8*) pBitRev);

    pBuf = (OMX_F64 *)
        (sizeof(OMX_FC64) * Nby2  + (OMX_S8*) pTwiddle);

    /* Bitreversed Index's */
    BitR = 0;
    /* only half is required */
    for (i = 1; i < Nby2; i++)
    {
        for (Val = Nby2 >> 1; BitR & Val; Val >>= 1)
        {
            BitR ^= Val;        
        }
        BitR ^= Val;
        pBitRev [i - 1] = BitR;
    }
    
    /* 
     * Filling Twiddle factors 
     *
     * W = (-2 * PI) / N 
     * N = 1 << order
     * W = -PI >> (order - 1)
     */
    W = -PI / Nby2;

    pTwiddle [0] . Re = 1.0;/*(OMX_S32)(1 * (1 << 15));*/
    pTwiddle [0] . Im = 0.0;
    for (i = 1; i < Nby2; i++)
    {
        pTwiddle[i].Re = (OMX_F64) cos (W * i);
        pTwiddle[i].Im = (OMX_F64) sin (W * i);
    }

    /* Update the structure */
    pFFTStruct->N = Nby2 << 1;
    pFFTStruct->pTwiddle = pTwiddle;
    pFFTStruct->pBitRev = pBitRev;
    pFFTStruct->pBuf = pBuf;

    return OMX_Sts_NoErr;
}

/*****************************************************************************
 *                              END OF FILE
 *****************************************************************************/

