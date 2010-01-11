/**
 * 
 * File Name:  armSP.h
 * OpenMAX DL: v1.0.2
 * Revision:   8916
 * Date:       Wednesday, October 31, 2007
 * 
 * (c) Copyright 2007 ARM Limited. All Rights Reserved.
 * 
 * 
 *   
 * File: armSP.h
 * Brief: Declares API's/Basic Data types used across the OpenMAX Signal Processing domain
 *
 */
#ifndef _armSP_H_
#define _armSP_H_

#include "omxtypes.h"

/** FFT Specific declarations */

#define OMX_ACSP_FFT_NULL   (0)
#define OMX_ACSP_MAX_FFT_ORDER  (12)
#define PI          (3.1415926535897932384626433832795)

typedef struct  ARMsFFTSpec_FC64_Tag 
{
    OMX_U32     N;
    OMX_U16     *pBitRev;    
    OMX_FC64    *pTwiddle;
    OMX_FC64     *pBuf;    
}ARMsFFTSpec_FC64;

typedef struct  ARMsFFTSpec_F32_Tag 
{
    OMX_U32     N;
    OMX_U16     *pBitRev;    
    OMX_FC32    *pTwiddle;
}ARMsFFTSpec_FC32;

typedef struct  ARMsFFTSpec_R_F32_Tag 
{
    OMX_U32     N;
    OMX_U16     *pBitRev;
    OMX_FC32    *pTwiddle;
    OMX_F32     *pBuf;    
}ARMsFFTSpec_R_FC32;

typedef struct  ARMsFFTSpec_R_F64_Tag 
{
    OMX_U32     N;
    OMX_U16     *pBitRev;
    OMX_FC64    *pTwiddle;
    OMX_F64     *pBuf;    
}ARMsFFTSpec_R_FC64;


#define armSP_CPLX_MUL(out, a, b)                                         \
{                                                                   \
    ((out)->Re) = (((a)->Re * (b)->Re) - ((a)->Im * (b)->Im));      \
    ((out)->Im) = (((a)->Re * (b)->Im) + ((a)->Im * (b)->Re));      \
}

#define armSP_CPLX_ADD(out, a, b)                                         \
{                                                                   \
    ((out)->Re) = (((a)->Re + (b)->Re));                            \
    ((out)->Im) = (((a)->Im + (b)->Im));                            \
}

#define armSP_CPLX_SUB(out, a, b)                                         \
{                                                                   \
    ((out)->Re) = (((a)->Re - (b)->Re));                            \
    ((out)->Im) = (((a)->Im - (b)->Im));                            \
}

#define armSP_CPLX_ADD_SUB_X(out, a, b)                                   \
{                                                                   \
    ((out)->Re) = (((a)->Re + (b)->Im));                            \
    ((out)->Im) = (((a)->Im - (b)->Re));                            \
}

#define armSP_CPLX_SUB_ADD_X(out, a, b)                                   \
{                                                                   \
    ((out)->Re) = (((a)->Re - (b)->Im));                            \
    ((out)->Im) = (((a)->Im + (b)->Re));                            \
}


#endif

/*End of File*/



