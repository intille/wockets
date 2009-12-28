/**
 * File: omxSP.h
 * Brief: OpenMAX DL v1.0.2 - Signal Processing library
 *
 * Copyright © 2005-07 The Khronos Group Inc. All Rights Reserved. 
 *
 * These materials are protected by copyright laws and contain material 
 * proprietary to the Khronos Group, Inc.  You may use these materials 
 * for implementing Khronos specifications, without altering or removing 
 * any trademark, copyright or other notice from the specification.
 * 
 * Khronos Group makes no, and expressly disclaims any, representations 
 * or warranties, express or implied, regarding these materials, including, 
 * without limitation, any implied warranties of merchantability or fitness 
 * for a particular purpose or non-infringement of any intellectual property. 
 * Khronos Group makes no, and expressly disclaims any, warranties, express 
 * or implied, regarding the correctness, accuracy, completeness, timeliness, 
 * and reliability of these materials. 
 *
 * Under no circumstances will the Khronos Group, or any of its Promoters, 
 * Contributors or Members or their respective partners, officers, directors, 
 * employees, agents or representatives be liable for any damages, whether 
 * direct, indirect, special or consequential damages for lost revenues, 
 * lost profits, or otherwise, arising from or in connection with these 
 * materials.
 * 
 * Khronos and OpenMAX are trademarks of the Khronos Group Inc. 
 *
 */

/* *****************************************************************************************/
/**
 *
 *  NewDomain: SP The Signal Processing Domain
 *  WithinDomain: OM
 *
 *  StartDomain: SP
 */


#ifndef _OMXSP_H_
#define _OMXSP_H_

#include "omxtypes.h"

#ifdef __cplusplus
extern "C" {
#endif


/* 2.1 FFT Data Structures */
 typedef void OMXFFTSpec_C_SC16;
 typedef void OMXFFTSpec_C_SC32;
 typedef void OMXFFTSpec_R_S16S32;
 typedef void OMXFFTSpec_R_S32;


/**
 * Function:  omxSP_Copy_S16   (2.2.1.1.1)
 *
 * Description:
 * Copies the len elements of the vector pointed to by pSrcinto the len 
 * elements of the vector pointed to by pDst. That is: 
 *     pDst[i] = pSrc[i], i=0, 1, ... , (len-1) 
 *
 * Input Arguments:
 *   
 *   pSrc - pointer to the source vector 
 *   len - number of elements contained in the source and destination vectors 
 *
 * Output Arguments:
 *   
 *   pDst - pointer to the destination vector 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments 
 *
 */
OMXResult omxSP_Copy_S16 (
    const OMX_S16 *pSrc,
    OMX_S16 *pDst,
    OMX_INT len
);



/**
 * Function:  omxSP_DotProd_S16   (2.2.2.1.1)
 *
 * Description:
 * Calculates the dot product of the two input vectors.  This function does 
 * not perform scaling.  The internal accumulator width must be at least 32 
 * bits.  If any of the partially accumulated values exceeds the range of a 
 * signed 32-bit integer then the result is undefined. 
 *
 * Input Arguments:
 *   
 *   pSrc1 - pointer to the first input vector; must be aligned on an 8-byte 
 *            boundary. 
 *   pSrc2 - pointer to the second input vector; must be aligned on an 8-byte 
 *            boundary. 
 *   len - length of the vectors in pSrc1 and pSrc2 
 *
 * Output Arguments:
 *
 * Return Value:
 *    
 *    The dot product result  Note: this function returns the actual result 
 *              rather than the standard OMXError. 
 *
 */
OMX_S32 omxSP_DotProd_S16 (
    const OMX_S16 *pSrc1,
    const OMX_S16 *pSrc2,
    OMX_INT len
);



/**
 * Function:  omxSP_DotProd_S16_Sfs   (2.2.2.1.2)
 *
 * Description:
 * Calculates the dot product of the two input signals with output scaling 
 * and saturation, i.e., the result is multiplied by two to the power of the 
 * negative (-)scalefactor (scaled) prior to return.  The result is saturated 
 * with rounding if the scaling operation produces a value outside the range 
 * of a signed 32-bit integer. Rounding behavior is defined in section 1.6.7 
 * Integer Scaling and Rounding Conventions. The internal accumulator width 
 * must be at least 32 bits. The result is undefined if any of the partially 
 * accumulated values exceeds the range of a signed 32-bit integer. 
 *
 * Input Arguments:
 *   
 *   pSrc1 - pointer to the first input vector; must be aligned on an 8-byte 
 *            boundary. 
 *   pSrc2 - pointer to the second input vector; must be aligned on an 8-byte 
 *            boundary. 
 *   len - length of the vectors in pSrc1 and pSrc2 
 *   scaleFactor - integer scalefactor 
 *
 * Output Arguments:
 *
 * Return Value:
 *    
 *    The dot product result  Note: This function returns the actual result 
 *              rather than the standard OMXError. 
 *
 */
OMX_S32 omxSP_DotProd_S16_Sfs (
    const OMX_S16 *pSrc1,
    const OMX_S16 *pSrc2,
    OMX_INT len,
    OMX_INT scaleFactor
);



/**
 * Function:  omxSP_BlockExp_S16   (2.2.2.2.2)
 *
 * Description:
 * Block exponent calculation for 16-bit and 32-bit signals (count leading 
 * sign bits). These functions compute the number of extra sign bits of all 
 * values in the 16-bit and 32-bit input vector pSrc and return the minimum 
 * sign bit count. This is also the maximum shift value that could be used in 
 * scaling the block of data. The functions BlockExp_S16and BlockExp_S32 
 * return the values 15 and 31, respectively, for input vectors in which all 
 * entries are equal to zero.  Note: These functions differs from other DL 
 * functions by not returning the standard OMXError but the actual result. 
 *
 * Input Arguments:
 *   
 *   pSrc - pointer to the input vector 
 *   len - number of elements contained in the input and output vectors (0 < 
 *            len < 65536) 
 *
 * Output Arguments:
 *   
 *   none 
 *
 * Return Value:
 *    
 *    Maximum exponent that may be used in scaling 
 *
 */
OMX_INT omxSP_BlockExp_S16 (
    const OMX_S16 *pSrc,
    OMX_INT len
);



/**
 * Function:  omxSP_BlockExp_S32   (2.2.2.2.2)
 *
 * Description:
 * Block exponent calculation for 16-bit and 32-bit signals (count leading 
 * sign bits). These functions compute the number of extra sign bits of all 
 * values in the 16-bit and 32-bit input vector pSrc and return the minimum 
 * sign bit count. This is also the maximum shift value that could be used in 
 * scaling the block of data. The functions BlockExp_S16and BlockExp_S32 
 * return the values 15 and 31, respectively, for input vectors in which all 
 * entries are equal to zero.  Note: These functions differs from other DL 
 * functions by not returning the standard OMXError but the actual result. 
 *
 * Input Arguments:
 *   
 *   pSrc - pointer to the input vector 
 *   len - number of elements contained in the input and output vectors (0 < 
 *            len < 65536) 
 *
 * Output Arguments:
 *   
 *   none 
 *
 * Return Value:
 *    
 *    Maximum exponent that may be used in scaling 
 *
 */
OMX_INT omxSP_BlockExp_S32 (
    const OMX_S32 *pSrc,
    OMX_INT len
);



/**
 * Function:  omxSP_FIR_Direct_S16   (2.2.3.1.1)
 *
 * Description:
 * omxSP_FIR_Direct_S16 and omxSP_FIR_Direct_S16_I Block FIR filtering for 
 * 16-bit data type.  This function applies the FIR filter defined by the 
 * coefficient vector pTapsQ15 to a vector of input data.  The result is 
 * saturated with rounding if the operation produces a value outside the range 
 * of a signed 16-bit integer.  Rounding behavior is defined in section 1.6.7 
 * Integer Scaling and Rounding Conventions. The internal accumulator width 
 * must be at least 32 bits.  The result is undefined if any of the partially 
 * accumulated values exceeds the range of a signed 32-bit integer. 
 * omxSP_FIR_Direct_S16_Sfs and omxSP_FIR_Direct_S16_Isfs Block FIR filtering 
 * for 16-bit data type. This function applies the FIR filter defined by the 
 * coefficient vector pTapsQ15 to a vector of input data.  The output is 
 * multiplied by 2 to the negative power of scalefactor (i.e., 2^-scalefactor) 
 * before returning to the caller. Scaling and rounding conventions are 
 * defined in section 1.6.7. The internal accumulator width must be at least 
 * 32 bits.  The result is undefined if any of the partially accumulated 
 * values exceeds the range of a signed 32-bit integer. 
 *
 * Input Arguments:
 *   
 *   pSrc, pSrcDst - pointer to the vector of input samples to which the 
 *            filter is applied 
 *   sampLen - the number of samples contained in the input and output 
 *            vectors 
 *   pTapsQ15 - pointer to the vector that contains the filter coefficients, 
 *            represented in Q0.15 format (defined in section 1.6.5). Given 
 *            that -32768=pTapsQ15(k)<32768, 0=k<tapsLen, the range on the 
 *            actual filter coefficients is -1 = bK <1, and therefore 
 *            coefficient normalization may be required during the filter 
 *            design process. 
 *   tapsLen - the number of taps, or, equivalently, the filter order + 1 
 *   pDelayLine - pointer to the 2 tapsLen -element filter memory buffer 
 *            (state). The user is responsible for allocation, initialization, 
 *            and de-allocation. The filter memory elements are initialized to 
 *            zero in most applications. 
 *   pDelayLineIndex - pointer to the filter memory index that is maintained 
 *            internally by the function. The user should initialize the value 
 *            of this index to zero. 
 *   scaleFactor - saturation fixed scalefactor (only for the scaled 
 *            function). 
 *
 * Output Arguments:
 *   
 *   pDst, pSrcDst - pointer to the vector of filtered output samples 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments 
 *
 */
OMXResult omxSP_FIR_Direct_S16 (
    const OMX_S16 *pSrc,
    OMX_S16 *pDst,
    OMX_INT sampLen,
    const OMX_S16 *pTapsQ15,
    OMX_INT tapsLen,
    OMX_S16 *pDelayLine,
    OMX_INT *pDelayLineIndex
);



/**
 * Function:  omxSP_FIR_Direct_S16_I   (2.2.3.1.1)
 *
 * Description:
 * omxSP_FIR_Direct_S16 and omxSP_FIR_Direct_S16_I Block FIR filtering for 
 * 16-bit data type.  This function applies the FIR filter defined by the 
 * coefficient vector pTapsQ15 to a vector of input data.  The result is 
 * saturated with rounding if the operation produces a value outside the range 
 * of a signed 16-bit integer.  Rounding behavior is defined in section 1.6.7 
 * Integer Scaling and Rounding Conventions. The internal accumulator width 
 * must be at least 32 bits.  The result is undefined if any of the partially 
 * accumulated values exceeds the range of a signed 32-bit integer. 
 * omxSP_FIR_Direct_S16_Sfs and omxSP_FIR_Direct_S16_Isfs Block FIR filtering 
 * for 16-bit data type. This function applies the FIR filter defined by the 
 * coefficient vector pTapsQ15 to a vector of input data.  The output is 
 * multiplied by 2 to the negative power of scalefactor (i.e., 2^-scalefactor) 
 * before returning to the caller. Scaling and rounding conventions are 
 * defined in section 1.6.7. The internal accumulator width must be at least 
 * 32 bits.  The result is undefined if any of the partially accumulated 
 * values exceeds the range of a signed 32-bit integer. 
 *
 * Input Arguments:
 *   
 *   pSrc, pSrcDst - pointer to the vector of input samples to which the 
 *            filter is applied 
 *   sampLen - the number of samples contained in the input and output 
 *            vectors 
 *   pTapsQ15- pointer to the vector that contains the filter coefficients, 
 *            represented in Q0.15 format (defined in section 1.6.5). Given 
 *            that -32768=pTapsQ15(k)<32768, 0=k<tapsLen, the range on the 
 *            actual filter coefficients is -1 = bK <1, and therefore 
 *            coefficient normalization may be required during the filter 
 *            design process. 
 *   tapsLen - the number of taps, or, equivalently, the filter order + 1 
 *   pDelayLine - pointer to the 2 tapsLen -element filter memory buffer 
 *            (state). The user is responsible for allocation, initialization, 
 *            and de-allocation. The filter memory elements are initialized to 
 *            zero in most applications. 
 *   pDelayLineIndex - pointer to the filter memory index that is maintained 
 *            internally by the function. The user should initialize the value 
 *            of this index to zero. 
 *   scaleFactor - saturation fixed scalefactor (only for the scaled 
 *            function). 
 *
 * Output Arguments:
 *   
 *   pDst, pSrcDst - pointer to the vector of filtered output samples 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments 
 *
 */
OMXResult omxSP_FIR_Direct_S16_I (
    OMX_S16 *pSrcDst,
    OMX_INT sampLen,
    const OMX_S16 *pTapsQ15,
    OMX_INT tapsLen,
    OMX_S16 *pDelayLine,
    OMX_INT *pDelayLineIndex
);



/**
 * Function:  omxSP_FIR_Direct_S16_Sfs   (2.2.3.1.1)
 *
 * Description:
 * omxSP_FIR_Direct_S16 and omxSP_FIR_Direct_S16_I Block FIR filtering for 
 * 16-bit data type.  This function applies the FIR filter defined by the 
 * coefficient vector pTapsQ15 to a vector of input data.  The result is 
 * saturated with rounding if the operation produces a value outside the range 
 * of a signed 16-bit integer.  Rounding behavior is defined in section 1.6.7 
 * Integer Scaling and Rounding Conventions. The internal accumulator width 
 * must be at least 32 bits.  The result is undefined if any of the partially 
 * accumulated values exceeds the range of a signed 32-bit integer. 
 * omxSP_FIR_Direct_S16_Sfs and omxSP_FIR_Direct_S16_Isfs Block FIR filtering 
 * for 16-bit data type. This function applies the FIR filter defined by the 
 * coefficient vector pTapsQ15 to a vector of input data.  The output is 
 * multiplied by 2 to the negative power of scalefactor (i.e., 2^-scalefactor) 
 * before returning to the caller. Scaling and rounding conventions are 
 * defined in section 1.6.7. The internal accumulator width must be at least 
 * 32 bits.  The result is undefined if any of the partially accumulated 
 * values exceeds the range of a signed 32-bit integer. 
 *
 * Input Arguments:
 *   
 *   pSrc, pSrcDst - pointer to the vector of input samples to which the 
 *            filter is applied 
 *   sampLen - the number of samples contained in the input and output 
 *            vectors 
 *   pTapsQ15 - pointer to the vector that contains the filter coefficients, 
 *            represented in Q0.15 format (defined in section 1.6.5). Given 
 *            that -32768=pTapsQ15(k)<32768, 0=k<tapsLen, the range on the 
 *            actual filter coefficients is -1 = bK <1, and therefore 
 *            coefficient normalization may be required during the filter 
 *            design process. 
 *   tapsLen - the number of taps, or, equivalently, the filter order + 1 
 *   pDelayLine - pointer to the 2 tapsLen -element filter memory buffer 
 *            (state). The user is responsible for allocation, initialization, 
 *            and de-allocation. The filter memory elements are initialized to 
 *            zero in most applications. 
 *   pDelayLineIndex - pointer to the filter memory index that is maintained 
 *            internally by the function. The user should initialize the value 
 *            of this index to zero. 
 *   scaleFactor - saturation fixed scalefactor (only for the scaled 
 *            function). 
 *
 * Output Arguments:
 *   
 *   pDst, pSrcDst - pointer to the vector of filtered output samples 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments 
 *
 */
OMXResult omxSP_FIR_Direct_S16_Sfs (
    const OMX_S16 *pSrc,
    OMX_S16 *pDst,
    OMX_INT sampLen,
    const OMX_S16 *pTapsQ15,
    OMX_INT tapsLen,
    OMX_S16 *pDelayLine,
    OMX_INT *pDelayLineIndex,
    OMX_INT scaleFactor
);



/**
 * Function:  omxSP_FIR_Direct_S16_ISfs   (2.2.3.1.1)
 *
 * Description:
 * omxSP_FIR_Direct_S16 and omxSP_FIR_Direct_S16_I Block FIR filtering for 
 * 16-bit data type.  This function applies the FIR filter defined by the 
 * coefficient vector pTapsQ15 to a vector of input data.  The result is 
 * saturated with rounding if the operation produces a value outside the range 
 * of a signed 16-bit integer.  Rounding behavior is defined in section 1.6.7 
 * Integer Scaling and Rounding Conventions. The internal accumulator width 
 * must be at least 32 bits.  The result is undefined if any of the partially 
 * accumulated values exceeds the range of a signed 32-bit integer. 
 * omxSP_FIR_Direct_S16_Sfs and omxSP_FIR_Direct_S16_Isfs Block FIR filtering 
 * for 16-bit data type. This function applies the FIR filter defined by the 
 * coefficient vector pTapsQ15 to a vector of input data.  The output is 
 * multiplied by 2 to the negative power of scalefactor (i.e., 2^-scalefactor) 
 * before returning to the caller. Scaling and rounding conventions are 
 * defined in section 1.6.7. The internal accumulator width must be at least 
 * 32 bits.  The result is undefined if any of the partially accumulated 
 * values exceeds the range of a signed 32-bit integer. 
 *
 * Input Arguments:
 *   
 *   pSrc, pSrcDst - pointer to the vector of input samples to which the 
 *            filter is applied 
 *   sampLen - the number of samples contained in the input and output 
 *            vectors 
 *   pTapsQ15 - pointer to the vector that contains the filter coefficients, 
 *            represented in Q0.15 format (defined in section 1.6.5). Given 
 *            that -32768=pTapsQ15(k)<32768, 0=k<tapsLen, the range on the 
 *            actual filter coefficients is -1 = bK <1, and therefore 
 *            coefficient normalization may be required during the filter 
 *            design process. 
 *   tapsLen - the number of taps, or, equivalently, the filter order + 1 
 *   pDelayLine - pointer to the 2 tapsLen -element filter memory buffer 
 *            (state). The user is responsible for allocation, initialization, 
 *            and de-allocation. The filter memory elements are initialized to 
 *            zero in most applications. 
 *   pDelayLineIndex - pointer to the filter memory index that is maintained 
 *            internally by the function. The user should initialize the value 
 *            of this index to zero. 
 *   scaleFactor - saturation fixed scalefactor (only for the scaled 
 *            function). 
 *
 * Output Arguments:
 *   
 *   pDst, pSrcDst - pointer to the vector of filtered output samples 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments 
 *
 */
OMXResult omxSP_FIR_Direct_S16_ISfs (
    OMX_S16 *pSrcDst,
    OMX_INT sampLen,
    const OMX_S16 *pTapsQ15,
    OMX_INT tapsLen,
    OMX_S16 *pDelayLine,
    OMX_INT *pDelayLineIndex,
    OMX_INT scaleFactor
);



/**
 * Function:  omxSP_FIROne_Direct_S16   (2.2.3.1.2)
 *
 * Description:
 * omxSP_FIROne_Direct_S16 and omxSP_FIROne_Direct_S16_I: Single-sample FIR 
 * filtering for 16-bit data type. These functions apply the FIR filter 
 * defined by the coefficient vector pTapsQ15 to a single sample of input 
 * data.  The result is saturated with rounding if the operation produces a 
 * value outside the range of a signed 16-bit integer.  Rounding behavior is 
 * defined in section 1.6.7 Integer Scaling and Rounding Conventions.  The 
 * internal accumulator width must be at least 32 bits.  The result is 
 * undefined if any of the partially accumulated values exceeds the range of a 
 * signed 32-bit integer. omxSP_FIROne_Direct_S16_Sfs and 
 * omxSP_FIROne_Direct_S16_ISfs: Single-sample FIR filtering for 16-bit data 
 * type. These functions apply the FIR filter defined by the coefficient 
 * vector pTapsQ15 to a single sample of input data. The output is multiplied 
 * by 2 to the negative power of scalefactor (i.e., 2^-scalefactor) before 
 * returning to the user. Scaling and rounding conventions are defined in 
 * section 1.6.7. The internal accumulator width must be at least 32 bits.  
 * The result is undefined if any of the partially accumulated values exceeds 
 * the range of a signed 32-bit integer. 
 *
 * Input Arguments:
 *   
 *   val, pValResult - the single input sample to which the filter is 
 *            applied. A pointer is used for the in-place version. 
 *   pTapsQ15- pointer to the vector that contains the filter coefficients, 
 *            represented in Q0.15 format (as defined in section 1.6.5). Given 
 *            that -32768=pTapsQ15(k)<32768, 0=k<tapsLen, the range on the 
 *            actual filter coefficients is -1 = bK <1, and therefore 
 *            coefficient normalization may be required during the filter 
 *            design process. 
 *   tapsLen - the number of taps, or, equivalently, the filter order + 1 
 *   pDelayLine - pointer to the 2 tapsLen -element filter memory buffer 
 *            (state). The user is responsible for allocation, initialization, 
 *            and de-allocation. The filter memory elements are initialized to 
 *            zero in most applications. 
 *   pDelayLineIndex - pointer to the filter memory index that is maintained 
 *            internally by the function. The user should initialize the value 
 *            of this index to zero. 
 *   scaleFactor - saturation fixed scaleFactor (only for the scaled 
 *            function) 
 *
 * Output Arguments:
 *   
 *   pResult, pValResult - pointer to the filtered output sample 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments 
 *
 */
OMXResult omxSP_FIROne_Direct_S16 (
    OMX_S16 val,
    OMX_S16 *pResult,
    const OMX_S16 *pTapsQ15,
    OMX_INT tapsLen,
    OMX_S16 *pDelayLine,
    OMX_INT *pDelayLineIndex
);



/**
 * Function:  omxSP_FIROne_Direct_S16_I   (2.2.3.1.2)
 *
 * Description:
 * omxSP_FIROne_Direct_S16 and omxSP_FIROne_Direct_S16_I: Single-sample FIR 
 * filtering for 16-bit data type. These functions apply the FIR filter 
 * defined by the coefficient vector pTapsQ15 to a single sample of input 
 * data.  The result is saturated with rounding if the operation produces a 
 * value outside the range of a signed 16-bit integer.  Rounding behavior is 
 * defined in section 1.6.7 Integer Scaling and Rounding Conventions.  The 
 * internal accumulator width must be at least 32 bits.  The result is 
 * undefined if any of the partially accumulated values exceeds the range of a 
 * signed 32-bit integer. omxSP_FIROne_Direct_S16_Sfs and 
 * omxSP_FIROne_Direct_S16_ISfs: Single-sample FIR filtering for 16-bit data 
 * type. These functions apply the FIR filter defined by the coefficient 
 * vector pTapsQ15 to a single sample of input data. The output is multiplied 
 * by 2 to the negative power of scalefactor (i.e., 2^-scalefactor) before 
 * returning to the user. Scaling and rounding conventions are defined in 
 * section 1.6.7. The internal accumulator width must be at least 32 bits.  
 * The result is undefined if any of the partially accumulated values exceeds 
 * the range of a signed 32-bit integer. 
 *
 * Input Arguments:
 *   
 *   val, pValResult - the single input sample to which the filter is 
 *            applied. A pointer is used for the in-place version. 
 *   pTapsQ15- pointer to the vector that contains the filter coefficients, 
 *            represented in Q0.15 format (as defined in section 1.6.5). Given 
 *            that -32768=pTapsQ15(k)<32768, 0=k<tapsLen, the range on the 
 *            actual filter coefficients is -1 = bK <1, and therefore 
 *            coefficient normalization may be required during the filter 
 *            design process. 
 *   tapsLen - the number of taps, or, equivalently, the filter order + 1 
 *   pDelayLine - pointer to the 2 tapsLen -element filter memory buffer 
 *            (state). The user is responsible for allocation, initialization, 
 *            and de-allocation. The filter memory elements are initialized to 
 *            zero in most applications. 
 *   pDelayLineIndex - pointer to the filter memory index that is maintained 
 *            internally by the function. The user should initialize the value 
 *            of this index to zero. 
 *   scaleFactor - saturation fixed scaleFactor (only for the scaled 
 *            function) 
 *
 * Output Arguments:
 *   
 *   pResult, pValResult - pointer to the filtered output sample 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments 
 *
 */
OMXResult omxSP_FIROne_Direct_S16_I (
    OMX_S16 *pValResult,
    const OMX_S16 *pTapsQ15,
    OMX_INT tapsLen,
    OMX_S16 *pDelayLine,
    OMX_INT *pDelayLineIndex
);



/**
 * Function:  omxSP_FIROne_Direct_S16_Sfs   (2.2.3.1.2)
 *
 * Description:
 * omxSP_FIROne_Direct_S16 and omxSP_FIROne_Direct_S16_I: Single-sample FIR 
 * filtering for 16-bit data type. These functions apply the FIR filter 
 * defined by the coefficient vector pTapsQ15 to a single sample of input 
 * data.  The result is saturated with rounding if the operation produces a 
 * value outside the range of a signed 16-bit integer.  Rounding behavior is 
 * defined in section 1.6.7 Integer Scaling and Rounding Conventions.  The 
 * internal accumulator width must be at least 32 bits.  The result is 
 * undefined if any of the partially accumulated values exceeds the range of a 
 * signed 32-bit integer. omxSP_FIROne_Direct_S16_Sfs and 
 * omxSP_FIROne_Direct_S16_ISfs: Single-sample FIR filtering for 16-bit data 
 * type. These functions apply the FIR filter defined by the coefficient 
 * vector pTapsQ15 to a single sample of input data. The output is multiplied 
 * by 2 to the negative power of scalefactor (i.e., 2^-scalefactor) before 
 * returning to the user. Scaling and rounding conventions are defined in 
 * section 1.6.7. The internal accumulator width must be at least 32 bits.  
 * The result is undefined if any of the partially accumulated values exceeds 
 * the range of a signed 32-bit integer. 
 *
 * Input Arguments:
 *   
 *   val, pValResult - the single input sample to which the filter is 
 *            applied. A pointer is used for the in-place version. 
 *   pTapsQ15- pointer to the vector that contains the filter coefficients, 
 *            represented in Q0.15 format (as defined in section 1.6.5). Given 
 *            that -32768=pTapsQ15(k)<32768, 0=k<tapsLen, the range on the 
 *            actual filter coefficients is -1 = bK <1, and therefore 
 *            coefficient normalization may be required during the filter 
 *            design process. 
 *   tapsLen - the number of taps, or, equivalently, the filter order + 1 
 *   pDelayLine - pointer to the 2 tapsLen -element filter memory buffer 
 *            (state). The user is responsible for allocation, initialization, 
 *            and de-allocation. The filter memory elements are initialized to 
 *            zero in most applications. 
 *   pDelayLineIndex - pointer to the filter memory index that is maintained 
 *            internally by the function. The user should initialize the value 
 *            of this index to zero. 
 *   scaleFactor - saturation fixed scaleFactor (only for the scaled 
 *            function) 
 *
 * Output Arguments:
 *   
 *   pResult, pValResult - pointer to the filtered output sample 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments 
 *
 */
OMXResult omxSP_FIROne_Direct_S16_Sfs (
    OMX_S16 val,
    OMX_S16 *pResult,
    const OMX_S16 *pTapsQ15,
    OMX_INT tapsLen,
    OMX_S16 *pDelayLine,
    OMX_INT *pDelayLineIndex,
    OMX_INT scaleFactor
);



/**
 * Function:  omxSP_FIROne_Direct_S16_ISfs   (2.2.3.1.2)
 *
 * Description:
 * omxSP_FIROne_Direct_S16 and omxSP_FIROne_Direct_S16_I: Single-sample FIR 
 * filtering for 16-bit data type. These functions apply the FIR filter 
 * defined by the coefficient vector pTapsQ15 to a single sample of input 
 * data.  The result is saturated with rounding if the operation produces a 
 * value outside the range of a signed 16-bit integer.  Rounding behavior is 
 * defined in section 1.6.7 Integer Scaling and Rounding Conventions.  The 
 * internal accumulator width must be at least 32 bits.  The result is 
 * undefined if any of the partially accumulated values exceeds the range of a 
 * signed 32-bit integer. omxSP_FIROne_Direct_S16_Sfs and 
 * omxSP_FIROne_Direct_S16_ISfs: Single-sample FIR filtering for 16-bit data 
 * type. These functions apply the FIR filter defined by the coefficient 
 * vector pTapsQ15 to a single sample of input data. The output is multiplied 
 * by 2 to the negative power of scalefactor (i.e., 2^-scalefactor) before 
 * returning to the user. Scaling and rounding conventions are defined in 
 * section 1.6.7. The internal accumulator width must be at least 32 bits.  
 * The result is undefined if any of the partially accumulated values exceeds 
 * the range of a signed 32-bit integer. 
 *
 * Input Arguments:
 *   
 *   val, pValResult - the single input sample to which the filter is 
 *            applied. A pointer is used for the in-place version. 
 *   pTapsQ15- pointer to the vector that contains the filter coefficients, 
 *            represented in Q0.15 format (as defined in section 1.6.5). Given 
 *            that -32768=pTapsQ15(k)<32768, 0=k<tapsLen, the range on the 
 *            actual filter coefficients is -1 = bK <1, and therefore 
 *            coefficient normalization may be required during the filter 
 *            design process. 
 *   tapsLen - the number of taps, or, equivalently, the filter order + 1 
 *   pDelayLine - pointer to the 2 tapsLen -element filter memory buffer 
 *            (state). The user is responsible for allocation, initialization, 
 *            and de-allocation. The filter memory elements are initialized to 
 *            zero in most applications. 
 *   pDelayLineIndex - pointer to the filter memory index that is maintained 
 *            internally by the function. The user should initialize the value 
 *            of this index to zero. 
 *   scaleFactor - saturation fixed scaleFactor (only for the scaled 
 *            function) 
 *
 * Output Arguments:
 *   
 *   pResult, pValResult - pointer to the filtered output sample 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments 
 *
 */
OMXResult omxSP_FIROne_Direct_S16_ISfs (
    OMX_S16 *pValResult,
    const OMX_S16 *pTapsQ15,
    OMX_INT tapsLen,
    OMX_S16 *pDelayLine,
    OMX_INT *pDelayLineIndex,
    OMX_INT scaleFactor
);



/**
 * Function:  omxSP_IIR_Direct_S16   (2.2.3.2.1)
 *
 * Description:
 * Block IIR filtering for 16-bit data. This function applies the direct form 
 * II IIR filter defined by the coefficient vector pTaps to a vector of input 
 * data. The internal accumulator width must be at least 32 bits, and the 
 * result is saturated if the operation produces a value outside the range of 
 * a signed 16-bit integer, i.e., the output will saturate to 0x8000 (-32768) 
 * for a negative overflow or 0x7fff (32767) for a positive overflow.  The 
 * result is undefined if any of the partially accumulated values exceeds the 
 * range of a signed 32-bit integer. 
 *
 * Input Arguments:
 *   
 *   pSrc, pSrcDst - pointer to the vector of input samples to which the 
 *            filter is applied 
 *   len - the number of samples contained in both the input and output 
 *            vectors 
 *   pTaps - pointer to the 2L+2-element vector that contains the combined 
 *            numerator and denominator filter coefficients from the system 
 *            transfer function, H(z). Coefficient scaling and coefficient 
 *            vector organization should follow the conventions described 
 *            above. The value of the coefficient scaleFactor exponent must be 
 *            non-negative (sf=0). 
 *   order - the maximum of the degrees of the numerator and denominator 
 *            coefficient polynomials from the system transfer function, H(z). 
 *            In the notation of section 2.2.3.2, the parameter 
 *            order=max(K,M)=L gives the maximum delay, in samples, used to 
 *            compute each output sample. 
 *   pDelayLine - pointer to the L-element filter memory buffer (state). The 
 *            user is responsible for allocation, initialization, and 
 *            deallocation. The filter memory elements are initialized to zero 
 *            in most applications. 
 *
 * Output Arguments:
 *   
 *   pDst, pSrcDst - pointer to the vector of filtered output samples 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments 
 *
 */
OMXResult omxSP_IIR_Direct_S16 (
    const OMX_S16 *pSrc,
    OMX_S16 *pDst,
    OMX_INT len,
    const OMX_S16 *pTaps,
    OMX_INT order,
    OMX_S32 *pDelayLine
);



/**
 * Function:  omxSP_IIR_Direct_S16_I   (2.2.3.2.1)
 *
 * Description:
 * Block IIR filtering for 16-bit data. This function applies the direct form 
 * II IIR filter defined by the coefficient vector pTaps to a vector of input 
 * data. The internal accumulator width must be at least 32 bits, and the 
 * result is saturated if the operation produces a value outside the range of 
 * a signed 16-bit integer, i.e., the output will saturate to 0x8000 (-32768) 
 * for a negative overflow or 0x7fff (32767) for a positive overflow.  The 
 * result is undefined if any of the partially accumulated values exceeds the 
 * range of a signed 32-bit integer. 
 *
 * Input Arguments:
 *   
 *   pSrc, pSrcDst - pointer to the vector of input samples to which the 
 *            filter is applied 
 *   len - the number of samples contained in both the input and output 
 *            vectors 
 *   pTaps - pointer to the 2L+2-element vector that contains the combined 
 *            numerator and denominator filter coefficients from the system 
 *            transfer function, H(z). Coefficient scaling and coefficient 
 *            vector organization should follow the conventions described 
 *            above. The value of the coefficient scaleFactor exponent must be 
 *            non-negative (sf=0). 
 *   order - the maximum of the degrees of the numerator and denominator 
 *            coefficient polynomials from the system transfer function, H(z). 
 *            In the notation of section 2.2.3.2, the parameter 
 *            order=max(K,M)=L gives the maximum delay, in samples, used to 
 *            compute each output sample. 
 *   pDelayLine - pointer to the L-element filter memory buffer (state). The 
 *            user is responsible for allocation, initialization, and 
 *            deallocation. The filter memory elements are initialized to zero 
 *            in most applications. 
 *
 * Output Arguments:
 *   
 *   pDst, pSrcDst - pointer to the vector of filtered output samples 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments 
 *
 */
OMXResult omxSP_IIR_Direct_S16_I (
    OMX_S16 *pSrcDst,
    OMX_INT len,
    const OMX_S16 *pTaps,
    OMX_INT order,
    OMX_S32 *pDelayLine
);



/**
 * Function:  omxSP_IIROne_Direct_S16   (2.2.3.2.2)
 *
 * Description:
 * Single sample IIR filtering for 16-bit data. This function applies the 
 * direct form II IIR filter defined by the coefficient vector pTaps to a 
 * single sample of input data.  The internal accumulator width must be at 
 * least 32 bits, and the result is saturated if the operation produces a 
 * value outside the range of a signed 16-bit integer, i.e., the output will 
 * saturate to 0x8000 (-32768) for a negative overflow or 0x7fff (32767) for a 
 * positive overflow. The result is undefined if any of the partially 
 * accumulated values exceeds the range of a signed 32-bit integer. 
 *
 * Input Arguments:
 *   
 *   val, pValResult - the single input sample to which the filter is 
 *            applied. A pointer is used for the in-place version. 
 *   pTaps - pointer to the 2L+2 -element vector that contains the combined 
 *            numerator and denominator filter coefficients from the system 
 *            transfer function, H(z). Coefficient scaling and coefficient 
 *            vector organization should follow the conventions described 
 *            above. The value of the coefficient scaleFactor exponent must be 
 *            non-negative (sf=0). 
 *   order - the maximum of the degrees of the numerator and denominator 
 *            coefficient polynomials from the system transfer function, H(z). 
 *            In the notation of section 2.2.3.2, the parameter 
 *            order=max(K,M)=L gives the maximum delay, in samples, used to 
 *            compute each output sample. 
 *   pDelayLine - pointer to the L-element filter memory buffer (state). The 
 *            user is responsible for allocation, initialization, and 
 *            deallocation. The filter memory elements are initialized to zero 
 *            in most applications. 
 *
 * Output Arguments:
 *   
 *   pResult, pValResult - pointer to the filtered output sample 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments 
 *
 */
OMXResult omxSP_IIROne_Direct_S16 (
    OMX_S16 val,
    OMX_S16 *pResult,
    const OMX_S16 *pTaps,
    OMX_INT order,
    OMX_S32 *pDelayLine
);



/**
 * Function:  omxSP_IIROne_Direct_S16_I   (2.2.3.2.2)
 *
 * Description:
 * Single sample IIR filtering for 16-bit data. This function applies the 
 * direct form II IIR filter defined by the coefficient vector pTaps to a 
 * single sample of input data.  The internal accumulator width must be at 
 * least 32 bits, and the result is saturated if the operation produces a 
 * value outside the range of a signed 16-bit integer, i.e., the output will 
 * saturate to 0x8000 (-32768) for a negative overflow or 0x7fff (32767) for a 
 * positive overflow. The result is undefined if any of the partially 
 * accumulated values exceeds the range of a signed 32-bit integer. 
 *
 * Input Arguments:
 *   
 *   val, pValResult - the single input sample to which the filter is 
 *            applied. A pointer is used for the in-place version. 
 *   pTaps - pointer to the 2L+2 -element vector that contains the combined 
 *            numerator and denominator filter coefficients from the system 
 *            transfer function, H(z). Coefficient scaling and coefficient 
 *            vector organization should follow the conventions described 
 *            above. The value of the coefficient scaleFactor exponent must be 
 *            non-negative (sf=0). 
 *   order - the maximum of the degrees of the numerator and denominator 
 *            coefficient polynomials from the system transfer function, H(z). 
 *            In the notation of section 2.2.3.2, the parameter 
 *            order=max(K,M)=L gives the maximum delay, in samples, used to 
 *            compute each output sample. 
 *   pDelayLine - pointer to the L-element filter memory buffer (state). The 
 *            user is responsible for allocation, initialization, and 
 *            deallocation. The filter memory elements are initialized to zero 
 *            in most applications. 
 *
 * Output Arguments:
 *   
 *   pResult, pValResult - pointer to the filtered output sample 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments 
 *
 */
OMXResult omxSP_IIROne_Direct_S16_I (
    OMX_S16 *pValResult,
    const OMX_S16 *pTaps,
    OMX_INT order,
    OMX_S32 *pDelayLine
);



/**
 * Function:  omxSP_IIR_BiQuadDirect_S16   (2.2.3.3.1)
 *
 * Description:
 * Block biquad IIR filtering for 16-bit data type. This function applies the 
 * direct form II biquad IIR cascade defined by the coefficient vector pTapsto 
 * a vector of input data.  The internal accumulator width must be at least 32 
 * bits, and the result is saturated if the operation produces a value outside 
 * the range of a signed 16-bit integer, i.e., the output will saturate to 
 * 0x8000 (-32768) for a negative overflow or 0x7fff (32767) for a positive 
 * overflow.  The result is undefined if any of the partially accumulated 
 * values exceeds the range of a signed 32-bit integer. 
 *
 * Input Arguments:
 *   
 *   pSrc, pSrcDst - pointer to the vector of input samples to which the 
 *            filter is applied 
 *   len - the number of samples contained in both the input and output 
 *            vectors 
 *   pTaps - pointer to the 6P -element vector that contains the combined 
 *            numerator and denominator filter coefficients from the biquad 
 *            cascade. Coefficient scaling and coefficient vector organization 
 *            should follow the conventions described above. The value of the 
 *            coefficient scaleFactor exponent must be non-negative. (sfp=0). 
 *   numBiquad - the number of biquads contained in the IIR filter cascade: 
 *            (P) 
 *   pDelayLine - pointer to the 2P -element filter memory buffer (state). 
 *            The user is responsible for allocation, initialization, and 
 *            de-allocation. The filter memory elements are initialized to 
 *            zero in most applications. 
 *
 * Output Arguments:
 *   
 *   pDst, pSrcDst - pointer to the vector of filtered output samples 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments 
 *
 */
OMXResult omxSP_IIR_BiQuadDirect_S16 (
    const OMX_S16 *pSrc,
    OMX_S16 *pDst,
    OMX_INT len,
    const OMX_S16 *pTaps,
    OMX_INT numBiquad,
    OMX_S32 *pDelayLine
);



/**
 * Function:  omxSP_IIR_BiQuadDirect_S16_I   (2.2.3.3.1)
 *
 * Description:
 * Block biquad IIR filtering for 16-bit data type. This function applies the 
 * direct form II biquad IIR cascade defined by the coefficient vector pTapsto 
 * a vector of input data.  The internal accumulator width must be at least 32 
 * bits, and the result is saturated if the operation produces a value outside 
 * the range of a signed 16-bit integer, i.e., the output will saturate to 
 * 0x8000 (-32768) for a negative overflow or 0x7fff (32767) for a positive 
 * overflow.  The result is undefined if any of the partially accumulated 
 * values exceeds the range of a signed 32-bit integer. 
 *
 * Input Arguments:
 *   
 *   pSrc, pSrcDst - pointer to the vector of input samples to which the 
 *            filter is applied 
 *   len - the number of samples contained in both the input and output 
 *            vectors 
 *   pTaps - pointer to the 6P -element vector that contains the combined 
 *            numerator and denominator filter coefficients from the biquad 
 *            cascade. Coefficient scaling and coefficient vector organization 
 *            should follow the conventions described above. The value of the 
 *            coefficient scaleFactor exponent must be non-negative. (sfp=0). 
 *   numBiquad - the number of biquads contained in the IIR filter cascade: 
 *            (P) 
 *   pDelayLine - pointer to the 2P -element filter memory buffer (state). 
 *            The user is responsible for allocation, initialization, and 
 *            de-allocation. The filter memory elements are initialized to 
 *            zero in most applications. 
 *
 * Output Arguments:
 *   
 *   pDst, pSrcDst - pointer to the vector of filtered output samples 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments 
 *
 */
OMXResult omxSP_IIR_BiQuadDirect_S16_I (
    OMX_S16 *pSrcDst,
    OMX_INT len,
    const OMX_S16 *pTaps,
    OMX_INT numBiquad,
    OMX_S32 *pDelayLine
);



/**
 * Function:  omxSP_IIROne_BiQuadDirect_S16   (2.2.3.3.2)
 *
 * Description:
 * Single-sample biquad IIR filtering for 16-bit data type. This function 
 * applies the direct form II biquad IIR cascade defined by the coefficient 
 * vector pTaps to a single sample of input data.  The internal accumulator 
 * width must be at least 32 bits, and the result is saturated if the 
 * operation produces a value outside the range of a signed 16-bit integer, 
 * i.e., the output will saturate to 0x8000 (-32768) for a negative overflow 
 * or 0x7fff (32767) for a positive overflow.  The result is undefined if any 
 * of the partially accumulated values exceeds the range of a signed 32-bit 
 * integer. 
 *
 * Input Arguments:
 *   
 *   val, pValResult - the single input sample to which the filter is 
 *            applied. A pointer is used for the in-place version. 
 *   pTaps - pointer to the 6P-element vector that contains the combined 
 *            numerator and denominator filter coefficients from the biquad 
 *            cascade. Coefficient scaling and coefficient vector organization 
 *            should follow the conventions described above. The value of the 
 *            coefficient scalefactor exponent must be non-negative: (sfp=0). 
 *   numBiquad - the number of biquads contained in the IIR filter cascade: 
 *            (P) 
 *   pDelayLine - pointer to the 2p-element filter memory buffer (state). The 
 *            user is responsible for allocation, initialization, and 
 *            deallocation. The filter memory elements are initialized to zero 
 *            in most applications. 
 *
 * Output Arguments:
 *   
 *   pResult, pValResult - pointer to the filtered output sample 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments 
 *
 */
OMXResult omxSP_IIROne_BiQuadDirect_S16 (
    OMX_S16 val,
    OMX_S16 *pResult,
    const OMX_S16 *pTaps,
    OMX_INT numBiquad,
    OMX_S32 *pDelayLine
);



/**
 * Function:  omxSP_IIROne_BiQuadDirect_S16_I   (2.2.3.3.2)
 *
 * Description:
 * Single-sample biquad IIR filtering for 16-bit data type. This function 
 * applies the direct form II biquad IIR cascade defined by the coefficient 
 * vector pTaps to a single sample of input data.  The internal accumulator 
 * width must be at least 32 bits, and the result is saturated if the 
 * operation produces a value outside the range of a signed 16-bit integer, 
 * i.e., the output will saturate to 0x8000 (-32768) for a negative overflow 
 * or 0x7fff (32767) for a positive overflow.  The result is undefined if any 
 * of the partially accumulated values exceeds the range of a signed 32-bit 
 * integer. 
 *
 * Input Arguments:
 *   
 *   val, pValResult - the single input sample to which the filter is 
 *            applied. A pointer is used for the in-place version. 
 *   pTaps - pointer to the 6P-element vector that contains the combined 
 *            numerator and denominator filter coefficients from the biquad 
 *            cascade. Coefficient scaling and coefficient vector organization 
 *            should follow the conventions described above. The value of the 
 *            coefficient scalefactor exponent must be non-negative: (sfp=0). 
 *   numBiquad - the number of biquads contained in the IIR filter cascade: 
 *            (P) 
 *   pDelayLine - pointer to the 2p-element filter memory buffer (state). The 
 *            user is responsible for allocation, initialization, and 
 *            deallocation. The filter memory elements are initialized to zero 
 *            in most applications. 
 *
 * Output Arguments:
 *   
 *   pResult, pValResult - pointer to the filtered output sample 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments 
 *
 */
OMXResult omxSP_IIROne_BiQuadDirect_S16_I (
    OMX_S16 *pValResult,
    const OMX_S16 *pTaps,
    OMX_INT numBiquad,
    OMX_S32 *pDelayLine
);



/**
 * Function:  omxSP_FilterMedian_S32   (2.2.3.4.1)
 *
 * Description:
 * This function computes the median over the region specified by the median 
 * mask for the every element of the input array. The median outputs are 
 * stored in the corresponding elements of the output vector. 
 *
 * Input Arguments:
 *   
 *   pSrc - pointer to the input vector 
 *   pSrcDst - pointer to the input vector 
 *   len - number of elements contained in the input and output vectors (0 < 
 *            len < 65536) 
 *   maskSize- median mask size; if an even value is specified, the function 
 *            subtracts 1 and uses the odd value of the filter mask for median 
 *            filtering (0 < maskSize < 256) 
 *
 * Output Arguments:
 *   
 *   pDst - pointer to the median-filtered output vector 
 *   pSrcDst - pointer to the median-filtered output vector 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments 
 *    OMX_StsSP_EvenMedianMaskSize - even mask size replaced by odd mask size 
 *
 */
OMXResult omxSP_FilterMedian_S32 (
    const OMX_S32 *pSrc,
    OMX_S32 *pDst,
    OMX_INT len,
    OMX_INT maskSize
);



/**
 * Function:  omxSP_FilterMedian_S32_I   (2.2.3.4.1)
 *
 * Description:
 * This function computes the median over the region specified by the median 
 * mask for the every element of the input array. The median outputs are 
 * stored in the corresponding elements of the output vector. 
 *
 * Input Arguments:
 *   
 *   pSrc - pointer to the input vector 
 *   pSrcDst - pointer to the input vector 
 *   len - number of elements contained in the input and output vectors (0 < 
 *            len < 65536) 
 *   maskSize- median mask size; if an even value is specified, the function 
 *            subtracts 1 and uses the odd value of the filter mask for median 
 *            filtering (0 < maskSize < 256) 
 *
 * Output Arguments:
 *   
 *   pDst - pointer to the median-filtered output vector 
 *   pSrcDst - pointer to the median-filtered output vector 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments 
 *    OMX_StsSP_EvenMedianMaskSize - even mask size replaced by odd mask size 
 *
 */
OMXResult omxSP_FilterMedian_S32_I (
    OMX_S32 *pSrcDst,
    OMX_INT len,
    OMX_INT maskSize
);



/**
 * Function:  omxSP_FFTInit_C_SC16   (2.2.4.1.2)
 *
 * Description:
 * These functions initialize the specification structures required for the 
 * complex FFT and IFFT functions. Desired block length is specified as an 
 * input. The function <FFTInit_C_SC16> is used to initialize the 
 * specification structures for functions <FFTFwd_CToC_SC16_Sfs> and 
 * <FFTInv_CToC_SC16_Sfs> The function <FFTInit_C_SC32> is used to initialize 
 * the specification structures for the functions <FFTFwd_CToC_SC32_Sfs> and 
 * <FFTInv_CToC_SC32_Sfs> Memory for the specification structure *pFFTSpec 
 * must be allocated prior to calling these functions and should be 4-byte 
 * aligned for omxSP_FFTInit_C_SC16 and 8-byte aligned for 
 * omxSP_FFTInit_C_SC32. The space required for *pFFTSpec, in bytes, can be 
 * determined using <FFTGetBufSize_C_SC16> and <FFTGetBufSize_C_SC32>, 
 * respectively, for the 16-bit and 32-bit functions. 
 *
 * Input Arguments:
 *   
 *   order - base-2 logarithm of the desired block length; valid in the range 
 *            [0,12] 
 *
 * Output Arguments:
 *   
 *   pFFTSpec - pointer to initialized specification structure 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments The function returns OMX_Sts_BadArgErr 
 *              if one or more of the following is true: The pointer pFFTSpec 
 *              is either NULL or violates the specified alignment 
 *              restriction. order < 0 or order > 12 
 *
 */
OMXResult omxSP_FFTInit_C_SC16 (
    OMXFFTSpec_C_SC16 *pFFTSpec,
    OMX_INT order
);



/**
 * Function:  omxSP_FFTInit_C_SC32   (2.2.4.1.2)
 *
 * Description:
 * These functions initialize the specification structures required for the 
 * complex FFT and IFFT functions. Desired block length is specified as an 
 * input. The function <FFTInit_C_SC16> is used to initialize the 
 * specification structures for functions <FFTFwd_CToC_SC16_Sfs> and 
 * <FFTInv_CToC_SC16_Sfs> The function <FFTInit_C_SC32> is used to initialize 
 * the specification structures for the functions <FFTFwd_CToC_SC32_Sfs> and 
 * <FFTInv_CToC_SC32_Sfs> Memory for the specification structure *pFFTSpec 
 * must be allocated prior to calling these functions and should be 4-byte 
 * aligned for omxSP_FFTInit_C_SC16 and 8-byte aligned for 
 * omxSP_FFTInit_C_SC32. The space required for *pFFTSpec, in bytes, can be 
 * determined using <FFTGetBufSize_C_SC16> and <FFTGetBufSize_C_SC32>, 
 * respectively, for the 16-bit and 32-bit functions. 
 *
 * Input Arguments:
 *   
 *   order - base-2 logarithm of the desired block length; valid in the range 
 *            [0,12] 
 *
 * Output Arguments:
 *   
 *   pFFTSpec - pointer to initialized specification structure 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments The function returns OMX_Sts_BadArgErr 
 *              if one or more of the following is true: The pointer pFFTSpec 
 *              is either NULL or violates the specified alignment 
 *              restriction. order < 0 or order > 12 
 *
 */
OMXResult omxSP_FFTInit_C_SC32 (
    OMXFFTSpec_C_SC32 *pFFTSpec,
    OMX_INT order
);



/**
 * Function:  omxSP_FFTInit_R_S16S32   (2.2.4.1.4)
 *
 * Description:
 * These functions initialize specification structures required for the real 
 * FFT and IFFT functions. The function <FFTInit_R_S16S32> is used to 
 * initialize the specification structures for functions 
 * <FFTFwd_RToCCS_S16S32_Sfs> and <FFTInv_CCSToR_S32S16_Sfs>. The function 
 * <FFTInit_R_S32> is used to initialize the specification structures for 
 * functions <FFTFwd_RToCCS_S32_Sfs> and <FFTInv_CCSToR_S32_Sfs>. Memory for 
 * *pFFTFwdSpec must be allocated before calling these function and should be 
 * 8-byte aligned. The number of bytes required for *pFFTFwdSpeccan be 
 * determined using <FFTGetBufSize_R_S16S32> and <FFTGetBufSize_R_S32>, 
 * respectively, for the 16-bit and 32-bit functions. 
 *
 * Input Arguments:
 *   
 *   order - base-2 logarithm of the desired block length; valid in the range 
 *            [0,12] 
 *
 * Output Arguments:
 *   
 *   pFFTFwdSpec - pointer to the initialized specification structure 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments The function returns OMX_Sts_BadArgErr 
 *              if one or more of the following is true: 
 *    The pointer pFFTFwdSpec is either NULL or violates the 8-byte alignment 
 *              restrictions 
 *    order < 0 or order> 12 
 *
 */
OMXResult omxSP_FFTInit_R_S16S32 (
    OMXFFTSpec_R_S16S32*pFFTFwdSpec,
    OMX_INT order
);



/**
 * Function:  omxSP_FFTInit_R_S32   (2.2.4.1.4)
 *
 * Description:
 * These functions initialize specification structures required for the real 
 * FFT and IFFT functions. The function <FFTInit_R_S16S32> is used to 
 * initialize the specification structures for functions 
 * <FFTFwd_RToCCS_S16S32_Sfs> and <FFTInv_CCSToR_S32S16_Sfs>. The function 
 * <FFTInit_R_S32> is used to initialize the specification structures for 
 * functions <FFTFwd_RToCCS_S32_Sfs> and <FFTInv_CCSToR_S32_Sfs>. Memory for 
 * *pFFTFwdSpec must be allocated before calling these function and should be 
 * 8-byte aligned. The number of bytes required for *pFFTFwdSpeccan be 
 * determined using <FFTGetBufSize_R_S16S32> and <FFTGetBufSize_R_S32>, 
 * respectively, for the 16-bit and 32-bit functions. 
 *
 * Input Arguments:
 *   
 *   order - base-2 logarithm of the desired block length; valid in the range 
 *            [0,12] 
 *
 * Output Arguments:
 *   
 *   pFFTFwdSpec - pointer to the initialized specification structure 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments The function returns OMX_Sts_BadArgErr 
 *              if one or more of the following is true: 
 *    The pointer pFFTFwdSpec is either NULL or violates the 8-byte alignment 
 *              restrictions 
 *    order < 0 or order> 12 
 *
 */
OMXResult omxSP_FFTInit_R_S32 (
    OMXFFTSpec_R_S32*pFFTFwdSpec,
    OMX_INT order
);



/**
 * Function:  omxSP_FFTGetBufSize_C_SC16   (2.2.4.1.6)
 *
 * Description:
 * order These functions compute the size of the specification structure 
 * required for the length 2 complex FFT and IFFT functions. The function 
 * <FFTGetBufSize_C_SC16> is used in conjunction with the 16-bit functions 
 * <FFTFwd_CToC_SC16_Sfs> and <FFTInv_CToC_SC16_Sfs>. The function 
 * <FFTGetBufSize_C_SC32> is used in conjunction with the 32-bit functions 
 * <FFTFwd_CToC_SC32_Sfs> and <FFTInv_CToC_SC32_Sfs>. 
 *
 * Input Arguments:
 *   
 *   order - base-2 logarithm of the desired block length; valid in the range 
 *            [0,12] 
 *
 * Output Arguments:
 *   
 *   pSize - pointer to the number of bytes required for the specification 
 *            structure 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments The function returns OMX_Sts_BadArgErr 
 *              if one or more of the following is true: 
 *    pSize is NULL 
 *    order < 0 or order> 12 
 *
 */
OMXResult omxSP_FFTGetBufSize_C_SC16 (
    OMX_INT order,
    OMX_INT *pSize
);



/**
 * Function:  omxSP_FFTGetBufSize_C_SC32   (2.2.4.1.6)
 *
 * Description:
 * order These functions compute the size of the specification structure 
 * required for the length 2 complex FFT and IFFT functions. The function 
 * <FFTGetBufSize_C_SC16> is used in conjunction with the 16-bit functions 
 * <FFTFwd_CToC_SC16_Sfs> and <FFTInv_CToC_SC16_Sfs>. The function 
 * <FFTGetBufSize_C_SC32> is used in conjunction with the 32-bit functions 
 * <FFTFwd_CToC_SC32_Sfs> and <FFTInv_CToC_SC32_Sfs>. 
 *
 * Input Arguments:
 *   
 *   order - base-2 logarithm of the desired block length; valid in the range 
 *            [0,12] 
 *
 * Output Arguments:
 *   
 *   pSize - pointer to the number of bytes required for the specification 
 *            structure 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments The function returns OMX_Sts_BadArgErr 
 *              if one or more of the following is true: 
 *    pSize is NULL 
 *    order < 0 or order> 12 
 *
 */
OMXResult omxSP_FFTGetBufSize_C_SC32 (
    OMX_INT order,
    OMX_INT *pSize
);



/**
 * Function:  omxSP_FFTGetBufSize_R_S16S32   (2.2.4.1.8)
 *
 * Description:
 * order These functions compute the size of the specification structure 
 * required for the length 2 real FFT and IFFT functions. The function 
 * <FFTGetBufSize_R_S16S32> is used in conjunction with the 16-bit functions 
 * <FFTFwd_RToCCS_S16S32_Sfs> and <FFTInv_CCSToR_S32S16_Sfs>. The function 
 * <FFTGetBufSize_R_S32> is used in conjunction with the 32-bit functions 
 * <FFTFwd_RToCCS_S32_Sfs> and <FFTInv_CCSToR_S32_Sfs>. 
 *
 * Input Arguments:
 *   
 *   order - base-2 logarithm of the length; valid in the range [0,12] 
 *
 * Output Arguments:
 *   
 *   pSize - pointer to the number of bytes required for the specification 
 *            structure 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments The function returns OMX_Sts_BadArgErr 
 *              if one or more of the following is true: 
 *    pSize is NULL 
 *    order < 0 or order> 12 
 *
 */
OMXResult omxSP_FFTGetBufSize_R_S16S32 (
    OMX_INT order,
    OMX_INT *pSize
);



/**
 * Function:  omxSP_FFTGetBufSize_R_S32   (2.2.4.1.8)
 *
 * Description:
 * order These functions compute the size of the specification structure 
 * required for the length 2 real FFT and IFFT functions. The function 
 * <FFTGetBufSize_R_S16S32> is used in conjunction with the 16-bit functions 
 * <FFTFwd_RToCCS_S16S32_Sfs> and <FFTInv_CCSToR_S32S16_Sfs>. The function 
 * <FFTGetBufSize_R_S32> is used in conjunction with the 32-bit functions 
 * <FFTFwd_RToCCS_S32_Sfs> and <FFTInv_CCSToR_S32_Sfs>. 
 *
 * Input Arguments:
 *   
 *   order - base-2 logarithm of the length; valid in the range [0,12] 
 *
 * Output Arguments:
 *   
 *   pSize - pointer to the number of bytes required for the specification 
 *            structure 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments The function returns OMX_Sts_BadArgErr 
 *              if one or more of the following is true: 
 *    pSize is NULL 
 *    order < 0 or order> 12 
 *
 */
OMXResult omxSP_FFTGetBufSize_R_S32 (
    OMX_INT order,
    OMX_INT *pSize
);



/**
 * Function:  omxSP_FFTFwd_CToC_SC16_Sfs   (2.2.4.2.2)
 *
 * Description:
 * order Compute an FFT for a complex signal of length of 2, where 0 <= order 
 * <= 12. Transform length is determined by the specification structure, which 
 * must be initialized prior to calling the FFT function using the appropriate 
 * helper, i.e., <FFTInit_C_sc32> or <FFTInit_C_SC16>.  The relationship 
 * between the input and output sequences can be expressed in terms of the 
 * DFT, i.e., 2p N -1 -j nk -scaleFactor N order X[k] =2  .x[]n  e , k 
 * =0,1,2,..., N -1; N =2 n=0 
 *
 * Input Arguments:
 *   order 
 *   pSrc - pointer to the input signal, a complex-valued vector of length 2; 
 *            must be aligned on an 8 byte boundary. 
 *   pFFTSpec - pointer to the preallocated and initialized specification 
 *            structure 
 *   scaleFactor - output scale factor; the range for 
 *            <omxSP_FFTFwd_CToC_SC16_Sfs> is [0,16], and for 
 *            <omxSP_FFTFwd_CToC_SC32_Sfs> the range is [0,32] 
 *
 * Output Arguments:
 *   order 
 *   pDst - pointer to the complex-valued output vector, of length 2; must be 
 *            aligned on an 8-byte boundary. 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - returned if one or more of the following conditions 
 *              is true: 
 *    -   one or more of the following pointers is NULL: pSrc, pDst, or 
 *              pFFTSpec. 
 *    -    pSrc or pDst is not 8-byte aligned scaleFactor<0 or scaleFactor 
 *              >16 for <omxSP_FFTFwd_CToC_SC16_Sfs> scaleFactor<0 or 
 *              scaleFactor >32 for <omxSP_FFTFwd_CToC_SC32_Sfs> 
 *
 */
OMXResult omxSP_FFTFwd_CToC_SC16_Sfs (
    const OMX_SC16 *pSrc,
    OMX_SC16 *pDst,
    const OMXFFTSpec_C_SC16 *pFFTSpec,
    OMX_INT scaleFactor
);



/**
 * Function:  omxSP_FFTFwd_CToC_SC32_Sfs   (2.2.4.2.2)
 *
 * Description:
 * order Compute an FFT for a complex signal of length of 2, where 0 <= order 
 * <= 12. Transform length is determined by the specification structure, which 
 * must be initialized prior to calling the FFT function using the appropriate 
 * helper, i.e., <FFTInit_C_sc32> or <FFTInit_C_SC16>.  The relationship 
 * between the input and output sequences can be expressed in terms of the 
 * DFT, i.e., 2p N -1 -j nk -scaleFactor N order X[k] =2  .x[]n  e , k 
 * =0,1,2,..., N -1; N =2 n=0 
 *
 * Input Arguments:
 *   order 
 *   pSrc - pointer to the input signal, a complex-valued vector of length 2; 
 *            must be aligned on an 8 byte boundary. 
 *   pFFTSpec - pointer to the preallocated and initialized specification 
 *            structure 
 *   scaleFactor - output scale factor; the range for 
 *            <omxSP_FFTFwd_CToC_SC16_Sfs> is [0,16], and for 
 *            <omxSP_FFTFwd_CToC_SC32_Sfs> the range is [0,32] 
 *
 * Output Arguments:
 *   order 
 *   pDst - pointer to the complex-valued output vector, of length 2; must be 
 *            aligned on an 8-byte boundary. 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - returned if one or more of the following conditions 
 *              is true: 
 *    -   one or more of the following pointers is NULL: pSrc, pDst, or 
 *              pFFTSpec. 
 *    -    pSrc or pDst is not 8-byte aligned scaleFactor<0 or scaleFactor 
 *              >16 for <omxSP_FFTFwd_CToC_SC16_Sfs> scaleFactor<0 or 
 *              scaleFactor >32 for <omxSP_FFTFwd_CToC_SC32_Sfs> 
 *
 */
OMXResult omxSP_FFTFwd_CToC_SC32_Sfs (
    const OMX_SC32 *pSrc,
    OMX_SC32 *pDst,
    const OMXFFTSpec_C_SC32 *pFFTSpec,
    OMX_INT scaleFactor
);



/**
 * Function:  omxSP_FFTInv_CToC_SC16_Sfs   (2.2.4.2.4)
 *
 * Description:
 * order These functions compute an inverse FFT for a complex signal of 
 * length of 2, where 0 <= order <= 12. Transform length is determined by the 
 * specification structure, which must be initialized prior to calling the FFT 
 * function using the appropriate helper, i.e., <FFTInit_C_sc32> or 
 * <FFTInit_C_SC16>. The relationship between the input and output sequences 
 * can be expressed in terms of the IDFT, i.e.,: 2p -scaleFactor N -1 2 N 
 *  order [] ej nk , n =0,1,2,...N -1; N =2 x[n] =  .Xk Nk=0 
 *
 * Input Arguments:
 *   order 
 *   pSrc - pointer to the complex-valued input signal, of length 2 ; must be 
 *            aligned on an 8-byte boundary. 
 *   pFFTSpec - pointer to the preallocated and initialized specification 
 *            structure 
 *   scaleFactor - scale factor of the output. Valid range for 
 *            <omxSP_FFTInv_CToC_SC16_Sfs> is [0,16] and for 
 *            <omxSP_FFTInv_CToC_SC32_Sfs> is [0,32]. 
 *
 * Output Arguments:
 *   order 
 *   pDst - pointer to the complex-valued output signal, of length 2; must be 
 *            aligned on an 8-byte boundary. 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - returned if one or more of the following conditions 
 *              is true: 
 *    -   one or more of the following pointers is NULL: pSrc, pDst, or 
 *              pFFTSpec. 
 *    -    pSrc or pDst is not 8-byte aligned scaleFactor<0 or scaleFactor 
 *              >16 for <omxSP_FFTInv_CToC_SC16_Sfs> scaleFactor<0 or 
 *              scaleFactor >32 for <omxSP_FFTFwd_CToC_SC32_Sfs> 
 *
 */
OMXResult omxSP_FFTInv_CToC_SC16_Sfs (
    const OMX_SC16 *pSrc,
    OMX_SC16 *pDst,
    const OMXFFTSpec_C_SC16 *pFFTSpec,
    OMX_INT scaleFactor
);



/**
 * Function:  omxSP_FFTInv_CToC_SC32_Sfs   (2.2.4.2.4)
 *
 * Description:
 * order These functions compute an inverse FFT for a complex signal of 
 * length of 2, where 0 <= order <= 12. Transform length is determined by the 
 * specification structure, which must be initialized prior to calling the FFT 
 * function using the appropriate helper, i.e., <FFTInit_C_sc32> or 
 * <FFTInit_C_SC16>. The relationship between the input and output sequences 
 * can be expressed in terms of the IDFT, i.e.,: 2p -scaleFactor N -1 2 N 
 *  order [] ej nk , n =0,1,2,...N -1; N =2 x[n] =  .Xk Nk=0 
 *
 * Input Arguments:
 *   order 
 *   pSrc - pointer to the complex-valued input signal, of length 2 ; must be 
 *            aligned on an 8-byte boundary. 
 *   pFFTSpec - pointer to the preallocated and initialized specification 
 *            structure 
 *   scaleFactor - scale factor of the output. Valid range for 
 *            <omxSP_FFTInv_CToC_SC16_Sfs> is [0,16] and for 
 *            <omxSP_FFTInv_CToC_SC32_Sfs> is [0,32]. 
 *
 * Output Arguments:
 *   order 
 *   pDst - pointer to the complex-valued output signal, of length 2; must be 
 *            aligned on an 8-byte boundary. 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - returned if one or more of the following conditions 
 *              is true: 
 *    -   one or more of the following pointers is NULL: pSrc, pDst, or 
 *              pFFTSpec. 
 *    -    pSrc or pDst is not 8-byte aligned scaleFactor<0 or scaleFactor 
 *              >16 for <omxSP_FFTInv_CToC_SC16_Sfs> scaleFactor<0 or 
 *              scaleFactor >32 for <omxSP_FFTFwd_CToC_SC32_Sfs> 
 *
 */
OMXResult omxSP_FFTInv_CToC_SC32_Sfs (
    const OMX_SC32 *pSrc,
    OMX_SC32 *pDst,
    const OMXFFTSpec_C_SC32 *pFFTSpec,
    OMX_INT scaleFactor
);



/**
 * Function:  omxSP_FFTFwd_RToCCS_S16S32_Sfs   (2.2.4.4.2)
 *
 * Description:
 * order These functions compute an FFT for a real-valued signal of length of 
 * 2, where 0 <= order <= 12. Transform length is determined by the 
 * specification structure, which must be initialized prior to calling the FFT 
 * function using the appropriate helper, i.e., <FFTInit_R_S16S32> or 
 * <FFTInit_R_S32>. The relationship between the input and output sequences 
 * can be expressed in terms of the DFT, i.e.,: 2p -scaleFactor N -1 2 N order 
 * [] =  .Xkjnk N 2 xn [] e , n =0,1,2,...N -1; = Nk =0 The 
 * conjugate-symmetric output sequence is represented using a packed RCCS 
 * vector, which is of length N+2, and is organized as follows: Index: 0 1 2 3 
 * 4 5 . . . N-2N-1     N N+1 Component R0 0   R1 I1 R2 I2 . . . RN/2-1 IN/2-1 
 * RN/2 0 where Rn and In, respectively, denote the real and imaginary 
 * components for FFT bin n. Bins are numbered from 0 to N/2, where N is the 
 * FFT length. Bin index 0 corresponds to the DC component, and bin index N/2 
 * corresponds to the foldover frequency. 
 *
 * Input Arguments:
 *   order 
 *   pSrc - pointer to the real-valued input sequence, of length 2; must be 
 *            aligned on an 8-byte boundary. 
 *   pFFTSpec - pointer to the preallocated and initialized specification 
 *            structure 
 *   scaleFactor - output scale factor; valid range is [0, 32] 
 *
 * Output Arguments:
 *   order 
 *   pDst - pointer to output sequence, represented using RCS format, of 
 *            length 2+2; must be aligned on an 8-byte boundary. 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments The function returns OMX_Sts_BadArgErr 
 *              if one or more of the following is true: 
 *    one of the pointers pSrc, pDst, pFFTSpec is NULL 
 *    pSrc, or pDst is not aligned on an 8-byte boundary 
 *    scaleFactor<0 or scaleFactor >32 
 *
 */
OMXResult omxSP_FFTFwd_RToCCS_S16S32_Sfs (
    const OMX_S16 *pSrc,
    OMX_S32 *pDst,
    const OMXFFTSpec_R_S16S32 *pFFTSpec,
    OMX_INT scaleFactor
);



/**
 * Function:  omxSP_FFTFwd_RToCCS_S32_Sfs   (2.2.4.4.2)
 *
 * Description:
 * order These functions compute an FFT for a real-valued signal of length of 
 * 2, where 0 <= order <= 12. Transform length is determined by the 
 * specification structure, which must be initialized prior to calling the FFT 
 * function using the appropriate helper, i.e., <FFTInit_R_S16S32> or 
 * <FFTInit_R_S32>. The relationship between the input and output sequences 
 * can be expressed in terms of the DFT, i.e.,: 2p -scaleFactor N -1 2 N order 
 * [] =  .Xkjnk N 2 xn [] e , n =0,1,2,...N -1; = Nk =0 The 
 * conjugate-symmetric output sequence is represented using a packed RCCS 
 * vector, which is of length N+2, and is organized as follows: Index: 0 1 2 3 
 * 4 5 . . . N-2N-1     N N+1 Component R0 0   R1 I1 R2 I2 . . . RN/2-1 IN/2-1 
 * RN/2 0 where Rn and In, respectively, denote the real and imaginary 
 * components for FFT bin n. Bins are numbered from 0 to N/2, where N is the 
 * FFT length. Bin index 0 corresponds to the DC component, and bin index N/2 
 * corresponds to the foldover frequency. 
 *
 * Input Arguments:
 *   order 
 *   pSrc - pointer to the real-valued input sequence, of length 2; must be 
 *            aligned on an 8-byte boundary. 
 *   pFFTSpec - pointer to the preallocated and initialized specification 
 *            structure 
 *   scaleFactor - output scale factor; valid range is [0, 32] 
 *
 * Output Arguments:
 *   order 
 *   pDst - pointer to output sequence, represented using RCS format, of 
 *            length 2+2; must be aligned on an 8-byte boundary. 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments The function returns OMX_Sts_BadArgErr 
 *              if one or more of the following is true: 
 *    one of the pointers pSrc, pDst, pFFTSpec is NULL 
 *    pSrc, or pDst is not aligned on an 8-byte boundary 
 *    scaleFactor<0 or scaleFactor >32 
 *
 */
OMXResult omxSP_FFTFwd_RToCCS_S32_Sfs (
    const OMX_S32 *pSrc,
    OMX_S32 *pDst,
    const OMXFFTSpec_R_S32 *pFFTSpec,
    OMX_INT scaleFactor
);



/**
 * Function:  omxSP_FFTInv_CCSToR_S32S16_Sfs   (2.2.4.4.4)
 *
 * Description:
 * These functions compute the inverse FFT for a conjugate-symmetric input 
 * sequence. Transform length is determined by the specification structure, 
 * which must be initialized prior to calling the FFT function using either 
 * <FFTInit_C_sc32> or <FFTInit_C_SC16>. For a transform of length M, the 
 * input sequence is represented using a packed RCCS vector of length M+2, and 
 * is organized as follows: Index: 0 1 2 34 5 . . . M-2 M-1 M M+1 Component R0 
 * 0   R1 I1 R2 I2   . . . RM/2-1 IM/2-1 RM/2 0 where Rn and In, respectively, 
 * denote the real and imaginary components for FFT bin n. Bins are numbered 
 * from 0 to M/2, where M is the FFT length. Bin index 0 corresponds to the DC 
 * component, and bin index M/2 corresponds to the foldover frequency. 
 *
 * Input Arguments:
 *   
 *   pSrc - pointer to the complex-valued input sequence represented using 
 *            RCCcs format, of length order 2+ 2; must be aligned on an 8-byte 
 *            boundary. 
 *   pFFTSpec - pointer to the preallocated and initialized specification 
 *            structure 
 *   scaleFactor - output scalefactor; range is [0,32] for the function 
 *            <omxSP_FFTInv_CCSToR_S32_Sfs>, and [0,16] for the function 
 *            <omxSP_FFTInv_CCSToR_S32S16_Sfs> 
 *
 * Output Arguments:
 *   order 
 *   pDst - pointer to the real-valued output sequence, of length 2 ; must be 
 *            aligned on an 8-byte boundary. 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments The function returns OMX_Sts_BadArgErr 
 *              if one or more of the following is true: 
 *    pSrc, pDst, or pFFTSpecis NULL 
 *    pSrcor pDstor pBufferis not aligned at 8-byte boundary 
 *    scaleFactor<0 or scaleFactor >16 for <omxSP_FFTInv_CCSToR_S32S16_Sfs> 
 *    scaleFactor<0 or scaleFactor >32 for <omxSP_FFTInv_CCSToR_S32_Sfs> 
 *
 */
OMXResult omxSP_FFTInv_CCSToR_S32S16_Sfs (
    const OMX_S32 *pSrc,
    OMX_S16 *pDst,
    const OMXFFTSpec_R_S16S32 *pFFTSpec,
    OMX_INT scaleFactor
);



/**
 * Function:  omxSP_FFTInv_CCSToR_S32_Sfs   (2.2.4.4.4)
 *
 * Description:
 * These functions compute the inverse FFT for a conjugate-symmetric input 
 * sequence. Transform length is determined by the specification structure, 
 * which must be initialized prior to calling the FFT function using either 
 * <FFTInit_C_sc32> or <FFTInit_C_SC16>. For a transform of length M, the 
 * input sequence is represented using a packed RCCS vector of length M+2, and 
 * is organized as follows: Index: 0 1 2 34 5 . . . M-2 M-1 M M+1 Component R0 
 * 0   R1 I1 R2 I2   . . . RM/2-1 IM/2-1 RM/2 0 where Rn and In, respectively, 
 * denote the real and imaginary components for FFT bin n. Bins are numbered 
 * from 0 to M/2, where M is the FFT length. Bin index 0 corresponds to the DC 
 * component, and bin index M/2 corresponds to the foldover frequency. 
 *
 * Input Arguments:
 *   
 *   pSrc - pointer to the complex-valued input sequence represented using 
 *            RCCcs format, of length order 2+ 2; must be aligned on an 8-byte 
 *            boundary. 
 *   pFFTSpec - pointer to the preallocated and initialized specification 
 *            structure 
 *   scaleFactor - output scalefactor; range is [0,32] for the function 
 *            <omxSP_FFTInv_CCSToR_S32_Sfs>, and [0,16] for the function 
 *            <omxSP_FFTInv_CCSToR_S32S16_Sfs> 
 *
 * Output Arguments:
 *   order 
 *   pDst - pointer to the real-valued output sequence, of length 2 ; must be 
 *            aligned on an 8-byte boundary. 
 *
 * Return Value:
 *    
 *    OMX_Sts_NoErr - no error 
 *    OMX_Sts_BadArgErr - bad arguments The function returns OMX_Sts_BadArgErr 
 *              if one or more of the following is true: 
 *    pSrc, pDst, or pFFTSpecis NULL 
 *    pSrcor pDstor pBufferis not aligned at 8-byte boundary 
 *    scaleFactor<0 or scaleFactor >16 for <omxSP_FFTInv_CCSToR_S32S16_Sfs> 
 *    scaleFactor<0 or scaleFactor >32 for <omxSP_FFTInv_CCSToR_S32_Sfs> 
 *
 */
OMXResult omxSP_FFTInv_CCSToR_S32_Sfs (
    const OMX_S32 *pSrc,
    OMX_S32 *pDst,
    const OMXFFTSpec_R_S32 *pFFTSpec,
    OMX_INT scaleFactor
);



#ifdef __cplusplus
}
#endif

#endif /** end of #define _OMXSP_H_ */

/** EOF */

