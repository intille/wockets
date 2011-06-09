/**
 * 
 * File Name:  armSP_FFT_CToC_SC32_Radix8.c
 * OpenMAX DL: v1.0.2
 * Revision:   8916
 * Date:       Wednesday, October 31, 2007
 * 
 * (c) Copyright 2007 ARM Limited. All Rights Reserved.
 * 
 * 
 * Description:
 * Compute a Radix 8 FFT stage for a N point complex signal
 */

#include "stdafx.h"
#include "omxtypes.h"
#include "armCOMM.h"
#include "armSP.h"




/**
 * Function: armSP_FFT_CToC_SC32_Radix8_OutOfPlace
 *
 * Description:
 * Compute a Radix 8 FFT stage for a complex signal of length 'Size',
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
 *                      pTwiddle[k] = exp(-j*(2*pi*k/size))  for 0<=k<(7*size/8)
 *
 * [in]  pSubFFTNum    pointer to the number of sub-FFT's completed so far
 * [out] pDst		   pointer to the complex-valued output vector, of
 *				        length 'Size'.Cannot be same as pSrc.
 *
 * Return Value:
 * Void
 *
 */

 
void armSP_FFT_CToC_SC32_Radix8_OutOfPlace(	
                OMX_FC64 *pSrc,
                OMX_FC64 *pTwiddle,
                OMX_FC64 *pDst,
                OMX_INT*  pSubFFTSize,
                OMX_INT*  pSubFFTNum )
                

{

    OMX_INT     set,grp,size,grpCount,grpSize,step;
    OMX_INT     setCount,grpStep,pointStep,outPointStep;
    OMX_FC64    *pTw1,*pTw2,*pTw3,*pTw4,*pTw5,*pTw6,*pTw7;
    OMX_FC64    *pT0,*pT1,*pT2,*pT3,*pT4,*pT5,*pT6,*pT7;
    OMX_FC64    *pU0,*pU1,*pU2,*pU3,*pU4,*pU5,*pU6,*pU7;
    OMX_FC64    *pV0,*pV1,*pV2,*pV3,*pV4,*pV5,*pV6,*pV7,*pTmpV5,*pTmpV7;
    OMX_FC64    *pOut0,*pOut1,*pOut2,*pOut3,*pOut4,*pOut5,*pOut6,*pOut7;
    OMX_FC64    *pTmpT1,*pTmpT2,*pTmpT3,*pTmpT4,*pTmpT5,*pTmpT6,*pTmpT7;
    OMX_FC64    Tmp1,Tmp2,Tmp3,Tmp4,Tmp5,Tmp6,Tmp7;
    OMX_FC64    U0,U1,U2,U3,U4,U5,U6,U7;
    OMX_FC64    V0,V1,V2,V3,V4,V5,V6,V7,TmpV5,TmpV7;
    OMX_F64     a;
    
    a           = 0.70710678118654752440084436210485;
    
    
    grpCount = *pSubFFTSize;
    grpSize  = *pSubFFTNum;
    size     = grpCount * grpSize;              /* size = length of input signal        */
    setCount = grpSize>>3;						/* setCount = grpSize/8 */
    step     = grpSize>>3;						/* step = step into the twiddle table  */
    grpStep  = grpSize;							/* grpStep  = size/grpCount */
    pointStep = setCount;                       /* Step into the 8 input radix-8 points */
    outPointStep   = size>>3;					/* Step into the output of radix-8 FFT */
    
    pOut0 = pDst;       pU0 = &U0;      pV0 = &V0;
    pTmpT1 = &Tmp1;		pU1 = &U1;		pV1 = &V1;
    pTmpT2 = &Tmp2;		pU2 = &U2;		pV2 = &V2;
    pTmpT3 = &Tmp3;		pU3 = &U3;		pV3 = &V3;
    pTmpT4 = &Tmp4;		pU4 = &U4;		pV4 = &V4;
    pTmpT5 = &Tmp5;		pU5 = &U5;		pV5 = &V5;
    pTmpT6 = &Tmp6;		pU6 = &U6;		pV6 = &V6;
    pTmpT7 = &Tmp7;		pU7 = &U7;		pV7 = &V7;
    
    pTmpV5  = &TmpV5;
    pTmpV7  = &TmpV7;
    
    
    for(grp = 0; grp < grpCount; grp++)
    {
    
        pTw1 = pTwiddle + grp*step;                 /* Load the twiddle factors for the grp */
        pTw2 = pTw1     + grp*step;
        pTw3 = pTw2     + grp*step;
        pTw4 = pTw3     + grp*step;
        pTw5 = pTw4     + grp*step;
        pTw6 = pTw5     + grp*step;
        pTw7 = pTw6     + grp*step;
        
        
        for(set = 0; set < setCount; set++)
        {
            pT0 = pSrc + (set + grp*grpStep);       /* 8 point FFT of each set */
            pT1 = pT0  + pointStep;
            pT2 = pT1  + pointStep;
            pT3 = pT2  + pointStep;
            pT4 = pT3  + pointStep;
            pT5 = pT4  + pointStep;
            pT6 = pT5  + pointStep;
            pT7 = pT6  + pointStep;
            
            pOut1 = pOut0 + outPointStep;
            pOut2 = pOut1 + outPointStep;
            pOut3 = pOut2 + outPointStep;
            pOut4 = pOut3 + outPointStep;
            pOut5 = pOut4 + outPointStep;
            pOut6 = pOut5 + outPointStep;
            pOut7 = pOut6 + outPointStep;
            
            
            armSP_CPLX_MUL (pTmpT1, pTw1, pT1);
            armSP_CPLX_MUL (pTmpT2, pTw2, pT2);
            armSP_CPLX_MUL (pTmpT3, pTw3, pT3);
            armSP_CPLX_MUL (pTmpT4, pTw4, pT4);
            armSP_CPLX_MUL (pTmpT5, pTw5, pT5);
            armSP_CPLX_MUL (pTmpT6, pTw6, pT6);
            armSP_CPLX_MUL (pTmpT7, pTw7, pT7);
            
            armSP_CPLX_ADD (pU0, pT0, pTmpT4); 
            armSP_CPLX_SUB (pU1, pT0, pTmpT4); 
            armSP_CPLX_ADD (pU2, pTmpT1, pTmpT5); 
            armSP_CPLX_SUB (pU3, pTmpT1, pTmpT5);
            armSP_CPLX_ADD (pU4, pTmpT2, pTmpT6); 
            armSP_CPLX_SUB (pU5, pTmpT2, pTmpT6);
            armSP_CPLX_ADD (pU6, pTmpT3, pTmpT7); 
            armSP_CPLX_SUB (pU7, pTmpT3, pTmpT7);
            
            armSP_CPLX_ADD (pV0, pU0, pU4); 
            armSP_CPLX_SUB (pV2, pU0, pU4); 
            armSP_CPLX_ADD (pV4, pU2, pU6); 
            armSP_CPLX_SUB (pV6, pU2, pU6); 
            armSP_CPLX_SUB_ADD_X (pV1, pU1, pU5);
            armSP_CPLX_ADD_SUB_X (pV3, pU1, pU5);
            armSP_CPLX_SUB_ADD_X (pV5, pU3, pU7);
            armSP_CPLX_ADD_SUB_X (pV7, pU3, pU7);
            
            armSP_CPLX_SUB_ADD_X (pTmpV5, pV5, pV5);
            armSP_CPLX_ADD_SUB_X (pTmpV7, pV7, pV7);
            pTmpV5->Re  *=  a;
            pTmpV5->Im  *=  a;
            pTmpV7->Re  *=  a;
            pTmpV7->Im  *=  a;
            
            armSP_CPLX_ADD (pOut0, pV0, pV4); 
            armSP_CPLX_SUB (pOut4, pV0, pV4); 
            armSP_CPLX_ADD (pOut7, pV1, pTmpV5); 
            armSP_CPLX_SUB (pOut3, pV1, pTmpV5);
            armSP_CPLX_SUB_ADD_X (pOut6, pV2, pV6);
            armSP_CPLX_ADD_SUB_X (pOut2, pV2, pV6);
            armSP_CPLX_ADD (pOut1, pV3, pTmpV7); 
            armSP_CPLX_SUB (pOut5, pV3, pTmpV7);
            
            
            
            pOut0 += 1; 
            
            
        }
    }
   
    /* Update the Grp count and size for the next stage */
    *pSubFFTSize = (*pSubFFTSize)<<3;
    *pSubFFTNum  = (*pSubFFTNum)>>3; 
    
}


/*****************************************************************************
 *                              END OF FILE
 *****************************************************************************/

