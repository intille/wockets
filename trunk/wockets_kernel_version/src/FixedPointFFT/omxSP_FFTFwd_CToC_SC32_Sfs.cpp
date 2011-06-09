/**
 * 
 * File Name:  omxSP_FFTFwd_CToC_SC32_Sfs.c
 * OpenMAX DL: v1.0.2
 * Revision:   8916
 * Date:       Wednesday, October 31, 2007
 * 
 * (c) Copyright 2007 ARM Limited. All Rights Reserved.
 * 
 * 
 * Description:
 * Compute a forward FFT for a complex signal
 */

#include "stdafx.h"
#include "omxtypes.h"
#include "armOMX.h"
#include "omxSP.h"
#include "armCOMM.h"
#include "armSP.h"

/**
 * Function: omxSP_FFTFwd_CToC_SC32_Sfs
 *
 * Description:
 * Compute a forward FFT for a complex signal of length of 2^order,
 * where 0 <= order <= 12.
 *
 * Remarks:
 * Transform length is determined by the specification structure, which must
 * be initialized prior to calling the FFT function using the appropriate helper,
 * i.e., <FFTInit_C_SC32>.
 *
 * Parameters:
 * [in]  pSrc       	pointer to the input signal, a complex-valued
 *				vector of length 2^order.
 * [in]  pFFTSpec     	pointer to the pre-allocated and initialized
 *				specification structure.
 * [in]  scaleFactor      output scale factor; the range is [0,32].
 * [out] pDst		pointer to the complex-valued output vector, of
 *				length 2^order.
 *
 * Return Value:
 * Standard omxError result. See enumeration for possible result codes.
 *
 */

OMXResult omxSP_FFTFwd_CToC_SC32_Sfs(
     const OMX_SC32 *pSrc,
     OMX_SC32 *pDst,
     const OMXFFTSpec_C_SC32 *pFFTSpec,
     OMX_INT scaleFactor
)
{
    OMX_INT     block, point;
    OMX_INT     i, j, N, NBy2;
    OMX_U16     *pRevIndex;
    OMX_FC64     *out;
    OMX_FC64    *pT1, *pT2, *pT, *pTw, T;
    ARMsFFTSpec_FC64 *pFFTStruct;

    /* Input parameter check */ 
    armRetArgErrIf(pSrc == NULL, OMX_Sts_BadArgErr)
    armRetArgErrIf(armNot32ByteAligned(pSrc), OMX_Sts_BadArgErr)
    armRetArgErrIf(pDst == NULL, OMX_Sts_BadArgErr)
    armRetArgErrIf(armNot32ByteAligned(pDst), OMX_Sts_BadArgErr)
    armRetArgErrIf(pFFTSpec == NULL, OMX_Sts_BadArgErr)
    armRetArgErrIf(scaleFactor < 0, OMX_Sts_BadArgErr)
    armRetArgErrIf(scaleFactor > 32, OMX_Sts_BadArgErr)

    /* Order range check */ 
    pFFTStruct = (ARMsFFTSpec_FC64 *) pFFTSpec;    
    N = pFFTStruct->N;
    armRetArgErrIf(N < 1, OMX_Sts_BadArgErr)
    armRetArgErrIf(N > (1 << 12), OMX_Sts_BadArgErr)
    
    /* Handle order zero case separate */
    if (N == 1)
    {
        pDst [0].Re = armSatRoundLeftShift_S32 (pSrc[0].Re, -scaleFactor);
        pDst [0].Im = armSatRoundLeftShift_S32 (pSrc[0].Im, -scaleFactor);
        return OMX_Sts_NoErr;        
    }
    
    /* Do fft in float */
    out = pFFTStruct->pBuf;

    /* bit reversal */    
    pRevIndex = pFFTStruct->pBitRev;
    for (i = 0; i < N; i++)
    {
        out [pRevIndex [i]].Re = (OMX_F64) pSrc [i]. Re;
        out [pRevIndex [i]].Im = (OMX_F64) pSrc [i]. Im;
    }
    
    NBy2 = N >> 1;
    pT = &T;
    point = 2;
    for (block = NBy2; block > 0; block >>= 1)
    {
        pTw = pFFTStruct->pTwiddle;
        for (i = 0; i < point / 2; i++)
        {
            pT1 = out + i;
            pT2 = pT1 + (point / 2);
            for (j = 0; j < block; j++)
            {
                armSP_CPLX_MUL (pT, pTw, pT2);
                armSP_CPLX_SUB (pT2, pT1, pT);
                armSP_CPLX_ADD (pT1, pT1, pT);
                pT1 += point;
                pT2 += point;
            }
            pTw += block;
        }
        point <<= 1;
    }
    

    /* revert back from float */
    for (i = 0; i < N; i++)
    {
        out [i].Re /= (1 << scaleFactor);
        out [i].Im /= (1 << scaleFactor);
        pDst [i]. Re = armSatRoundFloatToS32 (out [i].Re);
        pDst [i]. Im = armSatRoundFloatToS32 (out [i].Im);
    }
    
    return OMX_Sts_NoErr;
}
/*****************************************************************************
 *                              END OF FILE
 *****************************************************************************/

