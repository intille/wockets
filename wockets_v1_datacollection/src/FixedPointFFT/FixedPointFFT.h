// FixedPointFFT.h : main header file for the FixedPointFFT DLL
//

#pragma once

#ifndef __AFXWIN_H__
	#error "include 'stdafx.h' before including this file for PCH"
#endif

#include "resource.h"		// main symbols


// CFixedPointFFTApp
// See FixedPointFFT.cpp for the implementation of this class
//

class CFixedPointFFTApp : public CWinApp
{
public:
	CFixedPointFFTApp();

// Overrides
public:
	virtual BOOL InitInstance();

	DECLARE_MESSAGE_MAP()
};
