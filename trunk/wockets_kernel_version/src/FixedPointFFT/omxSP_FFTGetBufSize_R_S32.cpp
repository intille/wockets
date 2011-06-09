/**
 * 
 * File Name:  omxSP_FFTGetBufSize_R_S32.c
 * OpenMAX DL: v1.0.2
 * Revision:   8916
 * Date:       Wednesday, October 31, 2007
 * 
 * (c) Copyright 2007 ARM Limited. All Rights Reserved.
 * 
 * 
 * Description:
 * Computes the size of the specification structure required.
 */

#include "stdafx.h"
#include "omxtypes.h"
#include "armOMX.h"
#include "omxSP.h"
#include "armCOMM.h"
#include "armSP.h"

/**
 * Function: omxSP_FFTGetBufSize_R_S32
 *
 * Description:
 * Computes the size of the specification structure required for the length
 * 2^order real FFT and IFFT functions.
 *
 * Remarks:
 * This function is used in conjunction with the 32-bit functions
 * <FFTFwd_RToCCS_S32_Sfs> and <FFTInv_CCSToR_S32_Sfs>.
 *
 * Parameters:
 * [in]  order       base-2 logarithm of the length; valid in the range
 *			   [0,12].
 * [out] pSize	   pointer to the number of bytes required for the
 *			   specification structure.
 *
 * Return Value:
 * Standard omxError result. See enumeration for possible result codes.
 *
 */

OMXResult omxSP_FFTGetBufSize_R_S32(
     OMX_INT order,     
     OMX_INT *pSize
 )
{
    OMX_INT     NBy2;
    
    /* Input parameter check */ 
    armRetArgErrIf(pSize == NULL, OMX_Sts_BadArgErr)
    armRetArgErrIf(order < 0, OMX_Sts_BadArgErr)
    armRetArgErrIf(order > 12, OMX_Sts_BadArgErr)

    /* Check for order zero */
    if (order == 0)
    {
        *pSize = sizeof(ARMsFFTSpec_FC64);   
        return OMX_Sts_NoErr;
    }
    
    NBy2 = 1 << (order - 1);
    
    /* 2 pointers to store bitreversed array and twiddle factor array */
    *pSize = sizeof(ARMsFFTSpec_FC64)
    /* N bitreversed Numbers */
           + sizeof(OMX_U16) * NBy2
    /* Twiddle factors  */
           + sizeof(OMX_FC64) * NBy2
           + sizeof(OMX_F64) * (2 + (NBy2 << 1));

    return OMX_Sts_NoErr;
}

/*****************************************************************************
 *                              END OF FILE
 *****************************************************************************/

