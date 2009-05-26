/**
 * 
 * File Name:  armSP_FFT_CToC_SC32_Radix4.c
 * OpenMAX DL: v1.0.2
 * Revision:   8916
 * Date:       Wednesday, October 31, 2007
 * 
 * (c) Copyright 2007 ARM Limited. All Rights Reserved.
 * 
 * 
 * Description:
 * Compute a Radix 4 FFT stage for a N point complex signal
 */

#include "stdafx.h"
#include "omxtypes.h"
#include "armCOMM.h"
#include "armSP.h"



/**
 * 
 * Function: armSP_FFT_CToC_SC32_Radix4_InPlace
 *
 * Description:
 * Compute a Radix 4 FFT stage for a complex signal of length 'Size',
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
 *                      pTwiddle[k] = exp(-j*(2*pi*k/size))  for 0<=k<(3*size/4)
 *
 * [in]  pSubFFTNum    pointer to the number of sub-FFT's completed so far
 * [out] pDst		   pointer to the complex-valued output vector, of
 *				        length 'Size'.Can be same as pSrc.
 *
 * Return Value:
 * Void
 *
 */


void armSP_FFT_CToC_SC32_Radix4_InPlace(	
                OMX_FC64 *pSrc,
                OMX_FC64 *pTwiddle,
                OMX_FC64 *pDst,
                OMX_INT*  pSubFFTSize,
                OMX_INT*  pSubFFTNum )
                
{

    OMX_INT     set,grp,grpSize,step;
    OMX_INT     setCount,grpCount,setStep,pointStep;
    OMX_FC64    *pTw2,*pTw3,*pTw4,*pT1,*pT2,*pT3,*pT4,*pTmp1,*pTmp2,*pTmp3,*pTmp4,*pTmpT2,*pTmpT3,*pTmpT4;
    OMX_FC64    Tmp1,Tmp2,Tmp3,Tmp4,Tmp5,Tmp6,Tmp7;
    
    grpCount = *pSubFFTSize;
    grpSize  = *pSubFFTNum;
    step     = grpSize>>2;                      /* step = step into the twiddle table */     
    setCount = grpSize>>2;						/* setCount = grpSize/4 */
    setStep  = grpCount<<2;
    pointStep = grpCount;
    
    pTmp1 = &Tmp1;
    pTmp2 = &Tmp2;
    pTmp3 = &Tmp3;
    pTmp4 = &Tmp4;
    pTmpT2 = &Tmp5;
    pTmpT3 = &Tmp6;
    pTmpT4 = &Tmp7;
    
    for(grp = 0; grp < grpCount; grp++)
    {
    
        pTw2 = pTwiddle + grp*step;
        pTw3 = pTw2     + grp*step;
        pTw4 = pTw3     + grp*step;
        for(set = 0; set < setCount; set++)
        {
            pT1 = pSrc + (grp + set*setStep);
            pT2 = pT1  + pointStep;
            pT3 = pT2  + pointStep;
            pT4 = pT3  + pointStep;
            
            
            
            armSP_CPLX_MUL (pTmpT2, pTw2, pT2);
            armSP_CPLX_MUL (pTmpT3, pTw3, pT3);
            armSP_CPLX_MUL (pTmpT4, pTw4, pT4);
            
            
            armSP_CPLX_ADD (pTmp1, pT1, pTmpT3); 
            armSP_CPLX_SUB (pTmp2, pT1, pTmpT3); 
            armSP_CPLX_ADD (pTmp3, pTmpT2, pTmpT4); 
            armSP_CPLX_SUB (pTmp4, pTmpT2, pTmpT4);
            
            armSP_CPLX_ADD (pT1, pTmp1, pTmp3); 
            armSP_CPLX_SUB (pT3, pTmp1, pTmp3); 
            armSP_CPLX_SUB_ADD_X (pT4, pTmp2, pTmp4);
            armSP_CPLX_ADD_SUB_X (pT2, pTmp2, pTmp4);
            
            
            
            
        }
    }
    
    /* Update the Grp count and size for the next stage */
    *pSubFFTSize = (*pSubFFTSize)<<2;
    *pSubFFTNum  = (*pSubFFTNum)>>2;
    
}


/**
 * Function: armSP_FFT_CToC_SC32_Radix4_OutOfPlace
 *
 * Description:
 * Compute a Radix 4 FFT stage for a complex signal of length 'Size',
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
 *                      pTwiddle[k] = exp(-j*(2*pi*k/size))  for 0<=k<(3*size/4)
 *
 * [in]  pSubFFTNum    pointer to the number of sub-FFT's completed so far
 * [out] pDst		   pointer to the complex-valued output vector, of
 *				        length 'Size'.Cannot be same as pSrc.
 *
 * Return Value:
 * Void
 *
 */

 
void armSP_FFT_CToC_SC32_Radix4_OutOfPlace(	
                OMX_FC64 *pSrc,
                OMX_FC64 *pTwiddle,
                OMX_FC64 *pDst,
                OMX_INT*  pSubFFTSize,
                OMX_INT*  pSubFFTNum )
                

{

    OMX_INT     set,grp,size,grpCount,grpSize,step;
    OMX_INT     setCount,grpStep,pointStep,outPointStep;
    OMX_FC64    *pTw1,*pTw2,*pTw3,*pT0,*pT1,*pT2,*pT3,*pOut0,*pOut1,*pOut2,*pOut3;
    OMX_FC64    *pTmp0,*pTmp1,*pTmp2,*pTmp3,*pTmpT1,*pTmpT2,*pTmpT3;
    OMX_FC64    Tmp0,Tmp1,Tmp2,Tmp3,Tmp4,Tmp5,Tmp6;
    
    
    
    grpCount = *pSubFFTSize;
    grpSize  = *pSubFFTNum;
    size     = grpCount * grpSize;              /* size = length of input signal        */
    setCount = grpSize>>2;						/* setCount = grpSize/4 */
    step     = grpSize>>2;						/* step = step into the twiddle table  */
    grpStep  = grpSize;							/* grpStep  = size/grpCount */
    pointStep = setCount;                       /* Step into the 4 input radix-4 points */
    outPointStep   = size>>2;					/* Step into the output of radix-4 FFT */
    
    pOut0 = pDst;
    pTmp0 = &Tmp0;
    pTmp1 = &Tmp1;
    pTmp2 = &Tmp2;
    pTmp3 = &Tmp3;
    pTmpT1 = &Tmp4;
    pTmpT2 = &Tmp5;
    pTmpT3 = &Tmp6;
    
    for(grp = 0; grp < grpCount; grp++)
    {
    
        pTw1 = pTwiddle + grp*step;                 /* Load the twiddle factors for the grp */
        pTw2 = pTw1     + grp*step;
        pTw3 = pTw2     + grp*step;
        
        for(set = 0; set < setCount; set++)
        {
            pT0 = pSrc + (set + grp*grpStep);       /* 4 point FFT of each set */
            pT1 = pT0  + pointStep;
            pT2 = pT1  + pointStep;
            pT3 = pT2  + pointStep;
            pOut1 = pOut0 + outPointStep;
            pOut2 = pOut1 + outPointStep;
            pOut3 = pOut2 + outPointStep;
            
            
            armSP_CPLX_MUL (pTmpT1, pTw1, pT1);
            armSP_CPLX_MUL (pTmpT2, pTw2, pT2);
            armSP_CPLX_MUL (pTmpT3, pTw3, pT3);
            
            
            armSP_CPLX_ADD (pTmp0, pT0, pTmpT2); 
            armSP_CPLX_SUB (pTmp1, pT0, pTmpT2); 
            armSP_CPLX_ADD (pTmp2, pTmpT1, pTmpT3); 
            armSP_CPLX_SUB (pTmp3, pTmpT1, pTmpT3);
            
            armSP_CPLX_ADD (pOut0, pTmp0, pTmp2); 
            armSP_CPLX_SUB (pOut2, pTmp0, pTmp2); 
            armSP_CPLX_SUB_ADD_X (pOut3, pTmp1, pTmp3);
            armSP_CPLX_ADD_SUB_X (pOut1, pTmp1, pTmp3);
            
            pOut0 += 1; 
            
            
        }
    }
   
    /* Update the Grp count and size for the next stage */
    *pSubFFTSize = (*pSubFFTSize)<<2;
    *pSubFFTNum  = (*pSubFFTNum)>>2; 
    
}


/*****************************************************************************
 *                              END OF FILE
 *****************************************************************************/

