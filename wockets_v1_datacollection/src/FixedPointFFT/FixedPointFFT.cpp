// FixedPointFFT.cpp : Defines the initialization routines for the DLL.
//

#include "stdafx.h"
#include "FixedPointFFT.h"
#include "omxtypes.h"
#include "armOMX.h"
#include "omxSP.h"
#include "armCOMM.h"
#include "armSP.h"
#include <time.h>
#include <math.h>

#ifdef _DEBUG
#define new DEBUG_NEW
#endif

//
//TODO: If this DLL is dynamically linked against the MFC DLLs,
//		any functions exported from this DLL which call into
//		MFC must have the AFX_MANAGE_STATE macro added at the
//		very beginning of the function.
//
//		For example:
//
//		extern "C" BOOL PASCAL EXPORT ExportedFunction()
//		{
//			AFX_MANAGE_STATE(AfxGetStaticModuleState());
//			// normal function body here
//		}
//
//		It is very important that this macro appear in each
//		function, prior to any calls into MFC.  This means that
//		it must appear as the first statement within the 
//		function, even before any object variable declarations
//		as their constructors may generate calls into the MFC
//		DLL.
//
//		Please see MFC Technical Notes 33 and 58 for additional
//		details.
//


// CFixedPointFFTApp

BEGIN_MESSAGE_MAP(CFixedPointFFTApp, CWinApp)
END_MESSAGE_MAP()


// CFixedPointFFTApp construction

CFixedPointFFTApp::CFixedPointFFTApp()
{
	// TODO: add construction code here,
	// Place all significant initialization in InitInstance
}


// The one and only CFixedPointFFTApp object

CFixedPointFFTApp theApp;


// CFixedPointFFTApp initialization

BOOL CFixedPointFFTApp::InitInstance()
{
	CWinApp::InitInstance();

	return TRUE;
}

extern "C" _declspec(dllexport) int WINAPI multiply(int n1, int n2) 
{ 
    // Return the value of n1 and n2 multiplied together
    return(n1 * n2);
}


/**
The functions below ensure a 16 bit alignment for the allocated words

**/
void *malloc16(int size)
{
	char *block = new char[size + 19];
	int *aligned = (int*)((int)(block + 19) & 0xFFFFFFF0);
	aligned[-1] = (int)block;
	return aligned;
}

void free16(void *memory)
{
	delete ((int**)memory)[-1];
}


/**
The functions below ensure a 32 bit alignment for the allocated words
This works as follows, we create 35 additional redundant bytes
then we take the pointer to the allocated buffer size+35
and add to it 35, now
if we have 32 bit alignment we are ok and we are pointing to the required size,
if not, we look at the first previous 32 bit aligned word. Once, we find it, we store
the original address of the allocated buffer in the previous 4 bytes.

**/

void *malloc32(int size)
{
	char *block = new char[size + 259];
	int *aligned = (int*)((int)(block + 259) & 0xFFFFFF00);
	aligned[-1] = (int)block;
	return aligned;
}


void free32(void *memory)
{
	delete ((int**)memory)[-1];
}

static OMX_S32 *x;
static OMX_S32 *y;
static OMX_S32 *z;

static OMXFFTSpec_R_S32* pFwdSpec=NULL;
static OMXFFTSpec_R_S32* pInvSpec=NULL;
static int FFT_SIZE=256;
static int BIT_SIZE=8;


extern "C" _declspec(dllexport) void WINAPI InitializeBuffers(OMX_S32 **a1,OMX_S32 **a2,OMX_S32 **a3, int bitSize){

	OMX_INT bufSize;
	OMXResult status;
	FFT_SIZE=(int) pow((float)2,bitSize);
	BIT_SIZE= bitSize;
	x=*a1=(OMX_S32 *) malloc32(sizeof(OMX_S32)*FFT_SIZE);
	y=*a2=(OMX_S32 *) malloc32(sizeof(OMX_S32)*(FFT_SIZE+2));
	z=*a3=(OMX_S32 *) malloc32(sizeof(OMX_S32)*FFT_SIZE);
	status = omxSP_FFTGetBufSize_R_S32(BIT_SIZE, &bufSize);
	pFwdSpec = (OMXFFTSpec_R_S32 *) malloc(bufSize);
	pInvSpec = (OMXFFTSpec_R_S32 *) malloc(bufSize);
}

extern "C" _declspec(dllexport) void WINAPI CleanupBuffers(){

	free(pFwdSpec);
	free(pInvSpec);
	free32(x);
	free32(y);
	free32(z);
}
/**
Compute an FFT for a real-valued signal of length 2^order where
0<= order <=12. T

*/

extern "C" _declspec(dllexport) int WINAPI ComputeFFT()
{

	OMXResult status;

	
	status = omxSP_FFTInit_R_S32(pFwdSpec,BIT_SIZE);
	status = omxSP_FFTFwd_RToCCS_S32_Sfs(x,y,pFwdSpec,0);

	return 256;
}

extern "C" _declspec(dllexport) int WINAPI BenchmarkFFT()
{

	OMXResult status;
	srand(GetTickCount());
	for (int i=0;i<1000;i++){
		int* t = (int*)x;
         for (int j = 0; (j < FFT_SIZE); j++)
         {
                *(t + j) = (int) (rand()%1024);
                //s += " <" + i + "," + ((int)*(t + i)).ToString() + "> ";
         }

		status = omxSP_FFTInit_R_S32(pFwdSpec,BIT_SIZE);
		status = omxSP_FFTFwd_RToCCS_S32_Sfs(x,y,pFwdSpec,0);
	}
	return 256;
}




extern "C" _declspec(dllexport) int WINAPI ComputeInvFFT()
{

	OMXResult status;

	int* t = (int*)y;

	status = omxSP_FFTInit_R_S32(pInvSpec,BIT_SIZE);
	status = omxSP_FFTInv_CCSToR_S32_Sfs(y,z,pInvSpec,0);


	return 256;
}



extern "C" _declspec(dllexport) OMX_S32 WINAPI FixedDivide(OMX_S32 a, OMX_S32 b)
{

	return armIntDivAwayFromZero2 (a, b);
}

extern "C" _declspec(dllexport) OMX_S32 WINAPI FixedMultiply(OMX_S32 a, OMX_S32 b)
{

	return armSatMulS32S32_S32(a, b);
}

extern "C" _declspec(dllexport) OMX_S32 WINAPI FixedSubtract(OMX_S32 a, OMX_S32 b)
{

	return armSatSub_S32(a,b);
}

extern "C" _declspec(dllexport) OMX_S32 WINAPI FixedAdd(OMX_S32 a, OMX_S32 b)
{

	return armSatAdd_S32(a,b);
}