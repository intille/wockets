/**
 * 
 * File Name:  omxSP_IIR_BiQuadDirect_S16_I.c
 * OpenMAX DL: v1.0.2
 * Revision:   8916
 * Date:       Wednesday, October 31, 2007
 * 
 * (c) Copyright 2007 ARM Limited. All Rights Reserved.
 * 
 * 
 *
 * Description:
 * This file contains module for inplace block biquad IIR filtering
 *
 */

#include "stdafx.h"
#include "omxtypes.h"
#include "armOMX.h"
#include "omxSP.h"

/**
 * Function: omxSP_IIR_BiQuadDirect_S16_I
 *
 * Description:
 * Block biquad IIR filtering for 16-bit data type.
 *
 * Remarks:
 * This function applies the direct form II biquad IIR cascade defined by the
 * coefficient vector pTaps to a vector of input data.The output will saturate to 0x8000
 *(-32768) for a negative overflow or 0x7fff (32767) for a positive overflow.
 *
 * Parameters:
 * [in]  pSrcDst       	pointer to the vector of input samples to which
 *				the filter is applied.
 * [in]  len	     	the number of samples contained in both the
 *				input and output vectors.
 * [in]  pTaps      	pointer to the 6P element vector that contains
 * 				the combined numerator and denominator filter
 *				coefficients from the biquad cascade.
 *				Coefficient scaling and coefficient vector
 *				organization should follow the conventions
 *				described above. The value of the coefficient
 *				scalefactor exponent must be non-negative.
 *              (sfp >= 0)
 * [in]  numBiquad    	the number of biquads contained in the IIR
 *				filter cascade: (P).
 * [in]  pDelayLine       pointer to the 2P element filter memory
 *				buffer(state). The user is responsible for
 *				allocation, initialization, and de-allocation.
 *				The filter memory elements are initialized to
 *				zero
 * [out] pSrcDst		pointer to the filtered output samples.
 *
 * Return Value:
 * Standard omxError result. See enumeration for possible result codes.
 *
 */



OMXResult omxSP_IIR_BiQuadDirect_S16_I(
     OMX_S16 * pSrcDst,
     OMX_INT len,
     const OMX_S16 * pTaps,
     OMX_INT numBiquad,
     OMX_S32 * pDelayLine
 )
{

    OMXResult errorCode;
    
    errorCode = omxSP_IIR_BiQuadDirect_S16(
                        pSrcDst,
                        pSrcDst,
                        len,
                        pTaps,
                        numBiquad,
                        pDelayLine);

    return errorCode;

}

 /* End of File */

