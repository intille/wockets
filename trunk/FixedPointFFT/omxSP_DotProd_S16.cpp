/**
 * 
 * File Name:  omxSP_DotProd_S16.c
 * OpenMAX DL: v1.0.2
 * Revision:   8916
 * Date:       Wednesday, October 31, 2007
 * 
 * (c) Copyright 2007 ARM Limited. All Rights Reserved.
 * 
 * 
 *
 * Description:
 * This file contains module for Dot Product of two vectors
 *
 */

#include "stdafx.h"
#include "omxtypes.h"
#include "armOMX.h"
#include "omxSP.h"

/**
 * Function: omxSP_DotProd_S16
 *
 * Description:
 * Calculates the dot product of the two input vectors.  This function does not perform scaling.  
 * The internal accumulator width must be at least 32 bits.  
 * If any of the partially accumulated values exceeds the range of a signed 32-bit integer then the result is undefined.  
 * Remarks:
 * The function does not perform scaling.
 *
 * Note:
 * This function differs from other DL functions by not returning the standard
 * OMXError but the actual result.
 *
 * Parameters:
 * [in]  pSrc1      Pointer to the first input vector,must be aligned on an 8-byte boundary.
 * [in]  pSrc2      Pointer to the second input vector,must be aligned on an 8-byte boundary.
 * [in]  len        Length of the vector in pSrc and pDst.
 *
 * Return Value:
 * The dot product result.
 *
 */


OMX_S32 omxSP_DotProd_S16(
                            const OMX_S16 *pSrc1,
                            const OMX_S16 *pSrc2,
                            OMX_INT        len
                            )
{
    OMX_S32 DotProd;
    OMX_S32 Var1,Var2;
    
    /* Return if value 'len' is not valid */
    
    if(len <= 0)
    {
       return (OMX_S32)0;
    }
    
    /* Compute the DotProduct */
    
    DotProd = 0;
    
    do
    {
        Var1 = *pSrc1++;
        Var2 = *pSrc2++;
        
        DotProd += (OMX_S32)(Var1*Var2);
                
        len--;
        
    }while(len != 0);

    return DotProd;
} 
/* End of File */
