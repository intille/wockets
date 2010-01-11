/**
 * 
 * File Name:  omxSP_FIROne_Direct_S16.c
 * OpenMAX DL: v1.0.2
 * Revision:   8916
 * Date:       Wednesday, October 31, 2007
 * 
 * (c) Copyright 2007 ARM Limited. All Rights Reserved.
 * 
 * 
 * Description:
 *
 */

#include "stdafx.h"
#include "omxtypes.h"
#include "armOMX.h"
#include "omxSP.h"
#include "armCOMM.h"

/**
 * Function: omxSP_FIROne_Direct_S16
 *
 * Description:
 * Single-sample FIR filtering for 16-bit data type.
 *
 * Remarks:
 * This function applies the FIR filter defined by the coefficient vector
 * pTapsQ15 to a single sample of input data.
 *
 * Parameters:
 * [in]  val        the single input sample to which the filter is
 *              applied.
 * [in]  pTapsQ15       pointer to the vector that contains the filter
 *              coefficients, represented in Q0.15 format.
 *              Given that -32768<=pTapsQ15(k)<32768,
 *              0<=k<tapsLen, the range on the actual filter
 *              coefficients is: -1<=bk<1, and therefore
 *              coefficient normalization may be required
 *              during the filter design process.
 * [in]  tapsLen        the number of taps, e.g. the filter order + 1
 * [in]  pDelayLine       pointer to the 2*tapsLen-element filter memory
 *              buffer(state). The user is responsible for
 *              allocation, initialization, and de-allocation.
 *              The filter memory elements are initialized to
 *              zero in most applications.
 * [in]  pDelayLineIndex  pointer to the filter memory index that is
 *              maintained internally by the primitive. User
 *              should initialize the value of this index to
 *              zero.
 * [out] pResult        pointer to the filtered output sample
 *
 * Return Value:
 * Standard omxError result. See enumeration for possible result codes.
 *
 */

OMXResult omxSP_FIROne_Direct_S16(
     OMX_S16 val,
     OMX_S16 * pResult,
     const OMX_S16 * pTapsQ15,
     OMX_INT tapsLen,
     OMX_S16 * pDelayLine,
     OMX_INT * pDelayLineIndex
 )
 {
    OMX_U32 index;
    OMX_S32 accum;
    OMX_S16 *pDelayCurrent;

    /* Input parameter check */ 
    armRetArgErrIf((pResult == NULL), OMX_Sts_BadArgErr)
    armRetArgErrIf((pTapsQ15 == NULL), OMX_Sts_BadArgErr)
    armRetArgErrIf((tapsLen <= 0), OMX_Sts_BadArgErr)
    armRetArgErrIf((pDelayLine == NULL), OMX_Sts_BadArgErr)
    armRetArgErrIf((pDelayLineIndex == NULL), OMX_Sts_BadArgErr)
    armRetArgErrIf((*pDelayLineIndex < 0), OMX_Sts_BadArgErr)
    armRetArgErrIf((*pDelayLineIndex >= tapsLen), OMX_Sts_BadArgErr)

    /* Update the delay state */
    pDelayCurrent = &pDelayLine [*pDelayLineIndex];
    
    /* Copy input to current delay line position */
    pDelayCurrent [0] = pDelayCurrent [tapsLen] = val;

    accum = 0;
    for (index = 0; index < tapsLen; index++)
    {
        accum += (OMX_S32)pTapsQ15 [index] * 
                 (OMX_S32)pDelayCurrent [index]; 
    }
    
    if (--(*pDelayLineIndex) < 0)
    {
        *pDelayLineIndex = tapsLen - 1;     
    }
    
    /* Store the result */
    *pResult = armSatRoundLeftShift_S32(accum, -15);
    return OMX_Sts_NoErr;
 }


/*****************************************************************************
 *                              END OF FILE
 *****************************************************************************/

