/**
 * 
 * File Name:  armSP_FFT_CToC_SC32_Radix2.c
 * OpenMAX DL: v1.0.2
 * Revision:   8916
 * Date:       Wednesday, October 31, 2007
 * 
 * (c) Copyright 2007 ARM Limited. All Rights Reserved.
 * 
 * 
 * Description:
 * Compute a Radix 2 FFT stage for a N point complex signal
 */

#include "stdafx.h"
#include "omxtypes.h"
#include "armCOMM.h"
#include "armSP.h"




/**
 * 
 * Function: armSP_FFT_CToC_SC32_Radix2_InPlace
 *
 * Description:
 * Compute a Radix 2 FFT stage for a complex signal of length 'Size',
 * where 'size'  is an unsigned integer.  It does a in place computation.
 * The input for the first stage is required in bit reversed order.
 * 
 * The FFT is implemented using a decimation in time algorithm.
 * The input to each stage consists of 'SubFFTNum' completed FFT's of size 
 * 'SubFFTSize'. 
 *
 * The stage input and output buffer formats are defined as follows:
 *
 * SubFFTNum  (=R) The number of sub-FFT's completed so far
 * SubFFTSize (=S) The size of each sub-FFT completed so far
 * Size       (=N) The total FFT size
 *                 (N=R*S)
 *
 * (y[n*S],y[n*S+1],...,y[n*S+S-1]) = FFT_S(x[n'],x[n'+R],...,x[n'+R*(S-1)])
 * for 0<=n<R where n' is n bit reversed, x the original input data.
 * At the start of the FFT, R=N S=1. At the end of the FFT R=1, S=N.
 *
 * Within a radix-K stage we perform radix K butterflies. The terminology used here is:
 *
 * A 'set'   is a collection of K-inputs to the radix K butterfly
 * A 'group' is a collection of sets using the same twiddle factors
 *
 * Therefore within the stage:
 * group size = number of sets = SubFFTNum/K  &  number of groups = SubFFTSize
 * After a radix K stage SubFFTNum and SubFFTSize are updated.
 * At the end of the final stage GrpCount=N and GrpSize=1 so that the FFT is completed.
 *
 * 
 * Parameters:
 * [in]  pSrc          pointer to the input signal, a complex-valued
 *				        vector of length 'Size'.
 * [in]  pSubFFTSize   pointer to the size of each sub-FFT completed so far
 *				
 * [in]  pTwiddle      pointer to the twiddle table
 *                      pTwiddle[k] = exp(-j*(2*pi*k/size))  for 0<=k<(size/2)
 *
 * [in]  pSubFFTNum    pointer to the number of sub-FFT's completed so far
 * [out] pDst		   pointer to the complex-valued output vector, of
 *				        length 'Size'.Can be same as pSrc.
 *
 * Return Value:
 * Void
 *
 */
 


void armSP_FFT_CToC_SC32_Radix2_InPlace(	
                OMX_FC64 *pSrc,
                OMX_FC64 *pTwiddle,
                OMX_FC64 *pDst,
                OMX_INT*  pSubFFTSize,
                OMX_INT*  pSubFFTNum )

{

    OMX_INT     set,grp,grpSize,step;
    OMX_INT     setCount,grpCount,setStep,pointStep;
    OMX_FC64    *pTw,*pT1,*pT2,*pT, T;
    
    grpCount = *pSubFFTSize ;
    grpSize  = *pSubFFTNum;
    step     = grpSize>>1;                          /* step = step into the twiddle table */
    setCount = grpSize>>1;
    setStep  = grpCount<<1;
    pointStep = grpCount;
    
    
    pT = &T;
    
    for(grp = 0; grp < grpCount; grp++)
    {
    
        pTw = pTwiddle + grp*step;                  /* Load the twiddle factors for the grp */
        for(set = 0; set < setCount; set++)
        {
            pT1 = pSrc + (grp + set*setStep);
            pT2 = pT1  + pointStep;
            
            armSP_CPLX_MUL (pT, pTw, pT2);
            armSP_CPLX_SUB (pT2, pT1, pT);
            armSP_CPLX_ADD (pT1, pT1, pT); 
        }
    }
    
    /* Update the Grp count and size for the next stage */
    *pSubFFTSize  = (*pSubFFTSize )<<1;
    *pSubFFTNum  = (*pSubFFTNum)>>1;
    
}

/**
 * Function: armSP_FFT_CToC_SC32_Radix2_OutOfPlace
 *
 * Description:
 * Compute a Radix 2 FFT stage for a complex signal of length 'Size',
 * where 'size'  is an unsigned integer. 
 * It does a out of place computation.The input is required in Normal order.
 * 
 * The FFT is implemented using a decimation in time algorithm.
 * The input to each stage consists of 'SubFFTNum' completed FFT's of size 
 * 'SubFFTSize'. 
 *
 * The stage input and output buffer formats are defined as follows:
 *
 * SubFFTNum  (=R) The number of sub-FFT's completed so far
 * SubFFTSize (=S) The size of each sub-FFT completed so far
 * Size       (=N) The total FFT size
 *                 (N=R*S)
 *
 * (y[n],y[n+R],...,y[n+R*(S-1)]) = FFT_S(x[n],x[n+R],...,x[n+R*(S-1)]) 
 * for 0<=n<R where 'x' is the original input data .
 * At the start of the FFT, R=N S=1. At the end of the FFT R=1, S=N.
 *
 * Within a radix-K stage we perform radix K butterflies. The terminology used here is:
 *
 * A 'set'   is a collection of K-inputs to the radix K butterfly
 * A 'group' is a collection of sets using the same twiddle factors
 *
 * Therefore within the stage:
 * group size = number of sets = SubFFTNum/K  &  number of groups = SubFFTSize
 * After a radix K stage SubFFTNum and SubFFTSize are updated.
 * At the end of the final stage GrpCount=N and GrpSize=1 so that the FFT is completed.
 *
 *
 * 
 * Parameters:
 * [in]  pSrc          pointer to the input signal, a complex-valued
 *				        vector of length 'Size'.
 * [in]  pSubFFTSize   pointer to the size of each sub-FFT completed so far
 *				
 * [in]  pTwiddle      pointer to the twiddle table
 *                      pTwiddle[k] = exp(-j*(2*pi*k/size))  for 0<=k<(size/2)
 *
 * [in]  pSubFFTNum    pointer to the number of sub-FFT's completed so far
 * [out] pDst		   pointer to the complex-valued output vector, of
 *				        length 'Size'.Cannot be same as pSrc.
 *
 * Return Value:
 * Void
 *
 */

void armSP_FFT_CToC_SC32_Radix2_OutOfPlace(	
                OMX_FC64 *pSrc,
                OMX_FC64 *pTwiddle,
                OMX_FC64 *pDst,
                OMX_INT*  pSubFFTSize,
                OMX_INT*  pSubFFTNum )

{

    OMX_INT     set,grp,size,grpCount,grpSize,step;
    OMX_INT     setCount,grpStep,pointStep,outPointStep;
    OMX_FC64    *pTw,*pT0,*pT1,*pT,*pOut0,*pOut1, T;
    
    
    
    grpCount = *pSubFFTSize ;
    grpSize  = *pSubFFTNum;
    size     = grpCount * grpSize;                  /* size = length of input signal */
    setCount = grpSize>>1;                          /* setCount = grpSize/2 */
    step     = grpSize>>1;                          /* step = step into the twiddle table  */
    grpStep  = grpSize;                             /* grpStep  = size/grpCount */
    pointStep = setCount;                           /* Step into the 2 input radix-2 points */
    outPointStep   = size>>1;   					/* Step into the output of radix-2 FFT */
    pT = &T;
    pOut0 = pDst;
    
    for(grp = 0; grp < grpCount; grp++)
    {
    
        
        pTw = pTwiddle + grp*step;                  /* Load the twiddle factors for the grp */
        for(set = 0; set < setCount; set++)
        {
            pT0 = pSrc + (set + grp*grpStep);       /* 2 point FFT of each set */
            pT1 = pT0  + pointStep;
            pOut1 = pOut0 + outPointStep;
            
            armSP_CPLX_MUL (pT, pTw, pT1);
            armSP_CPLX_SUB (pOut1, pT0, pT);
            armSP_CPLX_ADD (pOut0, pT0, pT);
            pOut0 += 1; 
        }
    }
    
    /* Update the SubFFTSize and SubFFTNum for the next stage */
    *pSubFFTSize  = (*pSubFFTSize )<<1;
    *pSubFFTNum  = (*pSubFFTNum)>>1;
}

/*****************************************************************************
 *                              END OF FILE
 *****************************************************************************/

