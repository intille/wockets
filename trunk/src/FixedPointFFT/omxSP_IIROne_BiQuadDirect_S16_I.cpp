/**
 * 
 * File Name:  omxSP_IIROne_BiQuadDirect_S16_I.c
 * OpenMAX DL: v1.0.2
 * Revision:   8916
 * Date:       Wednesday, October 31, 2007
 * 
 * (c) Copyright 2007 ARM Limited. All Rights Reserved.
 * 
 * 
 *
 * Description:
 * This file contains module for inplace single sample biquad IIR filtering
 *
 */

#include "stdafx.h"
#include "omxtypes.h"
#include "armOMX.h"
#include "omxSP.h"
#include "armCOMM.h"


/**
 * Function: omxSP_IIROne_BiQuadDirect_S16_I
 *
 * Description:
 * Single-sample biquad IIR filtering for 16-bit data type.
 *
 * Remarks:
 * This function applies the direct form II biquad IIR cascade defined by the
 * coefficient vector pTaps to a single sample of input data.The output will saturate to 0x8000
 *(-32768) for a negative overflow or 0x7fff (32767) for a positive overflow.
 *
 * Parameters:
 * [in]  pValResult      	A pointer to the single input sample to which
 *				the filter is applied.
 * [in]  pTaps      	pointer to the 6P element vector that contains
 * 				the combined numerator and denominator filter
 *				coefficients from the biquad cascade.
 *				Coefficient scaling and coefficient vector
 *				organization should follow the conventions
 *			        described above. The value of the coefficient
 *				scalefactor exponent must be non-negative.
 *              (sfp >= 0)
 * [in]  numBiquad    	the number of biquads contained in the IIR
 *				filter cascade: (P).
 * [in]  pDelayLine       pointer to the 2P element filter memory
 *				buffer(state). The user is responsible for
 *				allocation, initialization, and de-allocation.
 *				The filter memory elements are initialized to
 *				zero
 * [out] pValResult	pointer to the filtered output sample.
 *
 * Return Value:
 * Standard omxError result. See enumeration for possible result codes.
 *
 */



OMXResult omxSP_IIROne_BiQuadDirect_S16_I(
     OMX_S16 * pValResult,
     const OMX_S16 * pTaps,
     OMX_INT numBiquad,
     OMX_S32 * pDelayLine
 )
{
    OMXResult errorCode;
    
    armRetArgErrIf(pValResult == NULL, OMX_Sts_BadArgErr)

    errorCode = omxSP_IIROne_BiQuadDirect_S16(
                        *pValResult,
                        pValResult,
                        pTaps,
                        numBiquad,
                        pDelayLine);

    return errorCode;
    
} 

/* End of File */
