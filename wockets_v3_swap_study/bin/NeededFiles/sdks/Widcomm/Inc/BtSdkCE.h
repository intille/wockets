/////////////////////////////////////////////////////////////////////////////
//
//  Name        BtSdkCE.h
//  $Header:
//
//  Function    this file facilitates linking with the correct interface
//              library, and acts as a meta-header for the Widcomm SDK 
//              headers
//
//  Date               Modification
//  ----------------------------------
//  26Sep2003   HZ     Create
//
//  Copyright (c) 2003-2006, Broadcom Corporation, All Rights Reserved.
//
//////////////////////////////////////////////////////////////////////////////

#pragma once
#if (_WIN32_WCE >= 0x501)
#pragma comment(lib, "btsdkce50.lib")
#else
#pragma comment(lib, "btsdkce30.lib")
#endif

#include "BtIfDefinitions.h"
#include "BtIfClasses.h"
#include "BtIfObexHeaders.h"
