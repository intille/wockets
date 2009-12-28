/**
 * 
 * File Name:  omxSP_DotProd_S16_Sfs.c
 * OpenMAX DL: v1.0.2
 * Revision:   8916
 * Date:       Wednesday, October 31, 2007
 * 
 * (c) Copyright 2007 ARM Limited. All Rights Reserved.
 * 
 * 
 *
 * Description:
 * This file contains module for dot product of two vectors
 *
 */

#include "stdafx.h"
#include "omxtypes.h"
#include "armOMX.h"
#include "omxSP.h"
#include "armCOMM.h"

/**
 * Function: omxSP_DotProd_S16_Sfs
 *
 * Description:
 * Calculate the dot product of the two input signals with output scaling
 * and saturation. The result is returned in 32 bits.
 * The output will be multiplied by 2 to the power of scalefactor before returning to the user.
 *
 * Remarks:
 * Same as omxSP_DotProd_S16, but the sums are saturated.  The scaling is saturated if scaleFactor < -1
 * The sums will be multiplied by 2 to the power of scalefactor before returning to the user.
 *
 * Note:
 * This function differs from other DL functions by not returning the
 * standard OMXError but the actual result.
 *
 * Parameters:
 * [in]  pSrc1      Pointer to the first input signal buffer.
 * [in]  pSrc2      Pointer to the second input signal buffer.
 * [in]  len        Length of the signals in pSrc and pDst.
 * [in]  scaleFactor    Integer scaling factor.
 *
 * Return Value:
 * The dot product result.
 *
 */

OMX_S32 omxSP_DotProd_S16_Sfs(
                            const OMX_S16 *pSrc1,
                            const OMX_S16 *pSrc2,
                            OMX_INT       len,
                            OMX_INT       scaleFactor
                            )
{
    OMX_S32 DotProd;
    OMX_S16 Var1,Var2;
    
    
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

    /* Scale the result of the operation */
    
    DotProd = armSatRoundLeftShift_S32(DotProd,-scaleFactor);
    
    return DotProd;
    

}

 /* End of File */
 
