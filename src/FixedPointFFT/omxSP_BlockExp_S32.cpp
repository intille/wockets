/**
 * 
 * File Name:  omxSP_BlockExp_S32.c
 * OpenMAX DL: v1.0.2
 * Revision:   8916
 * Date:       Wednesday, October 31, 2007
 * 
 * (c) Copyright 2007 ARM Limited. All Rights Reserved.
 * 
 * 
 *
 * Description:
 * This file contains module for block exponent computation
 *
 */

#include "stdafx.h"
#include "omxtypes.h"
#include "armOMX.h"
#include "omxSP.h"

/**
 * Function: omxSP_BlockExp_S32
 *
 * Description:
 * Block exponent calculation for 32-bit signals (count leading sign bits).
 *
 * Status: Design
 *
 * Remarks:
 * This function computes the number of extra sign bits of all values
 * in the 32-bit input vector pSrc and returns the minimum sign bit
 * count. This is also the maximum shift value that could be used in
 * scaling the block of data.
 *
 * Note:
 * This function differs from other DL functions by not returning the
 *       standard OMXError but the actual result.
 *
 * Parameters:
 * [in]  pSrc  Pointer to the input signal buffer.
 * [in]  len   Length of the signal in pSrc
 *
 * Return Value:
 * Maximum exponent that may be used in scaling.
 *
 */

OMX_S32 omxSP_BlockExp_S32(
                            const OMX_S32 *pSrc,
                            int            len
                            )
{

    OMX_S32 Var,MaxVar;
    OMX_S32 MinSignBits;


    /* Compute the Leading zeros */

    MaxVar = 0;

    do
    {
        Var = *pSrc++;

        /* Invert the bits of a Negative number */

        if(Var < 0)
        {
            Var = ~Var;
        }

        /* Compute the Maximum */

        if(Var > MaxVar)
        {
            MaxVar = Var;
        }

        len--;

    }while(len != 0);

    for (MinSignBits=31; (MaxVar>>(31-MinSignBits))!=0 ; MinSignBits--);


    return MinSignBits;
}

/* End of File */
