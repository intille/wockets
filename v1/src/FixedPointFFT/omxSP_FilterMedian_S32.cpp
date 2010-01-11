/**
 * 
 * File Name:  omxSP_FilterMedian_S32.c
 * OpenMAX DL: v1.0.2
 * Revision:   8916
 * Date:       Wednesday, October 31, 2007
 * 
 * (c) Copyright 2007 ARM Limited. All Rights Reserved.
 * 
 * 
 *
 * Description:
 * This file contains module for median filtering
 *
 */

#include "stdafx.h"
#include "omxtypes.h"
#include "armOMX.h"
#include "omxSP.h"
#include "armCOMM.h"

/**
 * Function: omxSP_FilterMedian_S32
 *
 * Description:
 * This function computes the median values for each element of the input
 * array, and stores the result in the output vector.
 *
 * Remarks:
 * This function computes the median values for each element of the input
 * array, and stores the result in the output vector.
 *
 * Parameters:
 * [in]  pSrc       pointer to input and output array
 * [in]  len        number of elements contained in the input and
 *			  output vectors (0 < len < 65536)
 * [in]  maskSize   median mask size. If an even value is specified,
 *			  the function subtracts 1 and uses the odd value
 *			  of the filter mask for median filtering
 *			  (0 < maskSize <= 256).
 * [out] pDst       pointer to input and output array
 *
 * Return Value:
 * Standard omxError result. See enumeration for possible result codes.
 *
 */

OMXResult omxSP_FilterMedian_S32(
     const OMX_S32 *pSrc,
     OMX_S32 *pDst,
     OMX_INT len,
     OMX_INT maskSize
 )
{

    OMX_S32 sortedData[256];
    OMX_S32 *pSort;
    const OMX_S32 *pTempSrc;
    
    OMX_S32 firstElement,lastElement,temp;
    
    OMX_INT maskByTwo,i,j,count;
    
    /* Argument Check */
    armRetArgErrIf( pSrc     == NULL  , OMX_Sts_BadArgErr);
    armRetArgErrIf( pDst     == NULL  , OMX_Sts_BadArgErr);
    armRetArgErrIf( len      <= 0     , OMX_Sts_BadArgErr);
    armRetArgErrIf( len      >= 65536 , OMX_Sts_BadArgErr);
    armRetArgErrIf( maskSize <= 0     , OMX_Sts_BadArgErr);
    armRetArgErrIf( maskSize >= 256   , OMX_Sts_BadArgErr);
    armRetArgErrIf( maskSize > len    , OMX_Sts_BadArgErr);

    
    /* Processing */
    if(!(maskSize & 1))
    {
        maskSize--;
    }
    
    maskByTwo = ((maskSize - 1)>>1);

    firstElement = pSrc[0];
    lastElement  = pSrc[len - 1];
    
    for(count = 0 ; count < len ; count ++)
    {
        pSort    =  sortedData;
        pTempSrc =  pSrc;
        
        /* Initialize the array */

        if ( count < maskByTwo )
        {
            for(i = 0 ; i < (maskByTwo - count) ; i++)
            {
                *pSort++ = firstElement;
            }

            for(i = 0; i <= count; i++)
            {
                *pSort++ = *pTempSrc++;
            }
        }
        else
        {
            for(i = 0; i <= maskByTwo; i++)
            {
                *pSort++ = *pTempSrc++;
            }

            pSrc++;
        }
        
        if ( (len - count - 1) < maskByTwo )
        {
            for(i = 0; i < (len - count - 1); i++)
            {
                *pSort++ = *pTempSrc++;
            }

            for(i = 0; i < ( maskByTwo - (len - count - 1) ); i++)
            {
                *pSort++ = lastElement;
            }
        }
        else
        {
            for(i = 0; i < maskByTwo; i++)
            {
                *pSort++ = *pTempSrc++;
            }
        }
    
        /*Sort the Data - Bubble sort implementation*/
        
        for(i = 0 ; i <= maskByTwo ; i++)
        {
            for(j = 0; j < (maskSize - 1 - i); j++ )
            {
                if(sortedData[j+1] < sortedData[j])
                {
                    temp             = sortedData[j];
                    sortedData[j]    = sortedData[j+1];
                    sortedData[j+1]  = temp;
                }
            
            }
        
        }

        *pDst = sortedData[maskByTwo];
        
        pDst++;
        
        
    }

    return OMX_Sts_NoErr;
}

