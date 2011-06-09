/**
 * 
 * File Name:  omxSP_Copy_S16.c
 * OpenMAX DL: v1.0.2
 * Revision:   8916
 * Date:       Wednesday, October 31, 2007
 * 
 * (c) Copyright 2007 ARM Limited. All Rights Reserved.
 * 
 * 
 *
 * Description:
 * This file contains module for vector copy
 *
 */

#include "stdafx.h"
#include "omxtypes.h"
#include "armOMX.h"
#include "omxSP.h"

#include "armCOMM.h"

/**
 * Function: omxSP_Copy_S16
 *
 * Description:
 * Vector copy for 16-bit type data.
 *
 * Remarks:
 * This function Copies the len elements of the vector pointed to by pSrc into
 * the len elements of the vector pointed to by pDst.
 * The function checks the alignment of the pointers and select the optimal way to copy.
 *
 * Parameters:
 * [in]  pSrc        pointer to the source vector
 * [in]  len         number of elements contained in the source and
 *             destination vectors
 * [out] pDst        pointer to the destination vector
 *
 * Return Value:
 * Standard OMXResult result. See enumeration for possible result codes.
 *
 */

OMXResult omxSP_Copy_S16(
     const OMX_S16 * pSrc,
     OMX_S16 * pDst,
     OMX_INT len
 )
{
    OMX_INT i;
    /* Argument Check */
    armRetArgErrIf( pSrc == NULL, OMX_Sts_BadArgErr);
    armRetArgErrIf( pDst == NULL, OMX_Sts_BadArgErr);
    armRetArgErrIf( len < 0, OMX_Sts_BadArgErr);
    
    /* Processing */    
    for (i = len; i > 0; i--) 
    {
        *pDst++ = *pSrc++;
    }

    return OMX_Sts_NoErr;
}

/*End of File*/


