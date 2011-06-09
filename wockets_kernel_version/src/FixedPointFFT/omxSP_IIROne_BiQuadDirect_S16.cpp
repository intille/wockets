/**
 * 
 * File Name:  omxSP_IIROne_BiQuadDirect_S16.c
 * OpenMAX DL: v1.0.2
 * Revision:   8916
 * Date:       Wednesday, October 31, 2007
 * 
 * (c) Copyright 2007 ARM Limited. All Rights Reserved.
 * 
 * 
 *
 * Description:
 * This file contains module for single sample biuad IIR filtering
 *
 */

#include "stdafx.h"
#include "omxtypes.h"
#include "armOMX.h"
#include "omxSP.h"
#include "armCOMM.h"
#include "armSP.h"


/**
 * Function: omxSP_IIROne_BiQuadDirect_S16
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
 * [in]  val       	the single input sample to which the filter is
 *				applied.
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
 * [out] pResult		pointer to the filtered output sample.
 *
 * Return Value:
 * Standard omxError result. See enumeration for possible result codes.
 *
 */

OMXResult omxSP_IIROne_BiQuadDirect_S16(
     OMX_S16 val,
     OMX_S16 * pResult,
     const OMX_S16 * pTaps,
     OMX_INT numBiquad,
     OMX_S32 * pDelayLine
 )
{

    OMX_S16 InOut;
    OMX_S32 Temp1,Temp2;
    OMX_S32 Mac;

    /* Argument Check */
    armRetArgErrIf( pResult    == NULL, OMX_Sts_BadArgErr);
    armRetArgErrIf( pDelayLine == NULL, OMX_Sts_BadArgErr);
    armRetArgErrIf( pTaps      == NULL, OMX_Sts_BadArgErr);
    armRetArgErrIf( numBiquad  <= 0   , OMX_Sts_BadArgErr);
    
    /* Processing */
    InOut = val;

    while(numBiquad != 0)
    {
        /* Argument Check */   
        armRetArgErrIf( pTaps[3] <  0     , OMX_Sts_BadArgErr);
    
        Temp1 = pDelayLine[0];
        Temp2 = pDelayLine[1];

        /* Accumulate Am's */

        Mac = armSatMac_S16S32_S32(0  , Temp1 , pTaps[4]);
        Mac = armSatMac_S16S32_S32(Mac, Temp2 , pTaps[5]);

        Mac = armSatSub_S32( armSatRoundLeftShift_S32(InOut, pTaps[3]) , Mac);
        Mac = armSatRoundLeftShift_S32(Mac,-pTaps[3]);
        
        /* Shift The DelayLine */

        pDelayLine[0] = Mac;
        pDelayLine[1] = Temp1;

        /* Accumulate Bk's */
                
        Mac = armSatMac_S16S32_S32(0  , Mac,   pTaps[0] );
        Mac = armSatMac_S16S32_S32(Mac, Temp1, pTaps[1] );
        Mac = armSatMac_S16S32_S32(Mac, Temp2, pTaps[2] );

        /* Output */
        InOut = armSatRoundRightShift_S32_S16(Mac, pTaps[3]);

        numBiquad--;

        pTaps += 6;
        pDelayLine += 2;
    
    }/*end while(numBiquad != 0)*/
                   
    *pResult = InOut;

    return OMX_Sts_NoErr;

}

 /* End of File */
