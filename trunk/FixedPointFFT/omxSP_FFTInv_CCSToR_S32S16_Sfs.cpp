/**
 * 
 * File Name:  omxSP_FFTInv_CCSToR_S32S16_Sfs.c
 * OpenMAX DL: v1.0.2
 * Revision:   8916
 * Date:       Wednesday, October 31, 2007
 * 
 * (c) Copyright 2007 ARM Limited. All Rights Reserved.
 * 
 * 
 * Description:
 * Computes an inverse FFT for a real-valued output sequence 
 */

#include "stdafx.h"
#include "omxtypes.h"
#include "armOMX.h"
#include "omxSP.h"
#include "armCOMM.h"
#include "armSP.h"

/**
 * Function: omxSP_FFTInv_CCSToR_S32_S16_Sfs
 *
 * Description:
 * Compute an inverse FFT for a real-valued output sequence of length of
 * 2^order,where 0 <= order <=12.
 *
 * Remarks:
 * Transform length is determined by the specification structure, which must be
 * initialized prior to calling the FFT function using the appropriate helper,
 * i.e., <FFTInit_R_S16_S32>. The conjugate-symmetric input sequence is
 * represented using a packed RCCS vector, which is of length N+2, and is
 * organized as follows:
 * Index:     0 1  2  3  4  5 . . .  N-2     N-1   N  N+1
 * Component R0 0 R1 I1 R2 I2 . . . RN/2-1 IN/2-1 RN/2 0
 *
 * Parameters:
 * [in]  pSrc       	pointer to the complex-valued input sequence
 *				represented using RCCcs format, of length
 *				2^order + 2.
 * [in]  pFFTSpec     	pointer to the pre-allocated and initialized
 *				specification structure.
 * [in]  scaleFactor      output scale factor; the range is [0,16].
 * [out] pDst		pointer to the real-valued output sequence,
 *				of length 2^order.
 *
 * Return Value:
 * Standard omxError result. See enumeration for possible result codes.
 *
 */

OMXResult omxSP_FFTInv_CCSToR_S32S16_Sfs(
     const OMX_S32 *pSrc,
     OMX_S16 *pDst,
     const OMXFFTSpec_R_S16S32 *pFFTSpec,
     OMX_INT scaleFactor
)
{
    ARMsFFTSpec_R_FC64 *pFFTStruct;
    OMX_INT     i, j, k, l, nBy2, size, N, NBy4, point, stage, offset;
    OMX_U16     *pRevIndex;
    OMX_F64     h, c, s, c1, c2, s1, s2, *out, ar, ai, br, bi, tr, ti;
    OMX_F64     c1r, c1i, c2r, c2i, t1r, t1i, t2r, t2i, z1r, z1i, z2r, z2i;
    OMX_F64     tmpr, tmpi;
    OMX_FC64    *pExp;

    /* Input parameter check */ 
    armRetArgErrIf(pSrc == NULL, OMX_Sts_BadArgErr)
    armRetArgErrIf(armNot32ByteAligned(pSrc), OMX_Sts_BadArgErr)
    armRetArgErrIf(pDst == NULL, OMX_Sts_BadArgErr)
    armRetArgErrIf(armNot32ByteAligned(pDst), OMX_Sts_BadArgErr)
    armRetArgErrIf(pFFTSpec == NULL, OMX_Sts_BadArgErr)
    armRetArgErrIf(scaleFactor < 0, OMX_Sts_BadArgErr)
    armRetArgErrIf(scaleFactor > 16, OMX_Sts_BadArgErr)

    /* Order range check */ 
    pFFTStruct = (ARMsFFTSpec_R_FC64 *) pFFTSpec;
    N = pFFTStruct->N;
    armRetArgErrIf(N < 1, OMX_Sts_BadArgErr)
    armRetArgErrIf(N > (1 << 12), OMX_Sts_BadArgErr)

    /* Handle order zero case separate */
    if (N == 1)
    {
        *pDst = armSatRoundRightShift_S32_S16(*pSrc, -scaleFactor);
        return OMX_Sts_NoErr;        
    }

    /* Do N/2 fft in float */
    out = pFFTStruct->pBuf;
    if (out == NULL)
    {
        return OMX_Sts_MemAllocErr;
    }
    
    for (i = 0; i < N + 2; i++)
    {
        out [i] = pSrc [i];
    }

    /* Real */
    h = 0.5;
    size = N;
    nBy2 = size >> 1;
    pExp = pFFTStruct->pTwiddle;
    
    for (i = 2, j = N - 2; i <= nBy2; i += 2, j -= 2)
    {
        c1r = out [i];     
        c1i = -out [i + 1];    
        c2r = out [j];     
        c2i = -out [j + 1];    
        z1r = out [i];     
        z1i = out [i + 1];    
        z2r = out [j];     
        z2i = out [j + 1];        
        
        /* CPLX_ADD (pT1, pZ2, pC1); */
        t1r = z2r + c1r;
        t1i = z2i + c1i;
        /* CPLX_SUB (pT2, pZ2, pC1); */
        t2r = z2r - c1r;
        t2i = z2i - c1i;
        /* CPLX_ADD (pC1, pZ1, pC2); */
        c1r = z1r + c2r;
        c1i = z1i + c2i;
        /* CPLX_SUB (pC2, pZ1, pC2); */
        c2r = z1r - c2r;
        c2i = z1i - c2i;

        c1 = pExp[i >> 1].Re;
        s1 = -pExp[i >> 1].Im;
        c2 = pExp[j >> 1].Re;
        s2 = -pExp[j >> 1].Im;

        /* CPLX_MUL (pZ1, pC2, pE1); */
        z1r = c2r*c1 - c2i*s1;
        z1i = c2r*s1 + c2i*c1;
        /* CPLX_MUL (pZ2, pT2, pE2); */
        z2r = t2r*c2 - t2i*s2;
        z2i = t2r*s2 + t2i*c2;
        
        c2r = -z1i;
        c2i = z1r;
        t2r = -z2i;
        t2i = z2r;

        out [i] = h * (c2r + c1r);        
        out [i + 1] = h * (c2i + c1i);
        
        out [j] = h * (t2r + t1r); 
        out [j + 1] = h * (t2i + t1i);
    }

    out [0] = h * ((c1r = out [0]) + out [N]);
    out [1] = h * (c1r - out [N]);   
    
    /* bit reversal */    
    pRevIndex = pFFTStruct->pBitRev;
    for (i = 2; i < N; i += 2)
    {
        j = 2 * pRevIndex [(i >> 1) - 1];
        if (i < j)
        {
            /* Swap */
            tmpr = out [j];
            tmpi = out [j + 1];
            out [j] = out [i];
            out [j + 1] = out [i + 1];
            out [i] = tmpr;
            out [i + 1] = tmpi;
        }
    }

    NBy4 = N >> 2;
    point = 2;
    for (stage = NBy4; stage > 0; stage >>= 1)
    {
        l = 0;
        for (i = 0; i < point; i += 2)
        {
            c = pExp[l << 1].Re;
            s = -pExp[l << 1].Im;

            k = point + i;
            offset = 0;
            for (j = 0; j < stage; j++)
            {                
                ar = out [offset + i];
                ai = out [offset + i + 1];
                br = out [offset + k];
                bi = out [offset + k + 1];
                /* B * W */
                tr = c*br - s*bi;
                ti = c*bi + s*br;

                out [offset + k] = ar - tr;
                out [offset + k + 1] = ai - ti;
                out [offset + i] = ar + tr;
                out [offset + i + 1] = ai + ti;

                offset += (2 * point);
            }
            l += stage;
        }
        point <<= 1;
    }

    /* revert back from float */
    for (i = 0; i < N; i += 2)
    {
        h = (1 << scaleFactor) * nBy2;
        out [i] /= h;
        out [i + 1] /= h;
        pDst [i] = armSatRoundFloatToS16 (out [i]);
        pDst [i + 1] = armSatRoundFloatToS16 (out [i + 1]);

    }

    return OMX_Sts_NoErr;
}

/*****************************************************************************
 *                              END OF FILE
 *****************************************************************************/

