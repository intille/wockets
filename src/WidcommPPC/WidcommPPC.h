// WidcommPPC.h : main header file for the WidcommPPC DLL
//

#pragma once

#ifndef __AFXWIN_H__
	#error "include 'stdafx.h' before including this file for PCH"
#endif

#include "BtSdkCE.h"
#include "resourceppc.h"


#define BLUETOOTH_MAX_NAME_SIZE 248

typedef ULONGLONG BTH_ADDR;
		static HANDLE  stackMutex;   
	class WidcommStackPPC : public CBtIf, public CSppClient, public CRfCommPort
		{
		public:
			 WidcommStackPPC();
			virtual ~WidcommStackPPC();
			virtual void OnDeviceResponded(BD_ADDR bda, DEV_CLASS devClass, BD_NAME bdName, BOOL bConnected);
			virtual void OnInquiryComplete(BOOL bSuccess, short nResponses);
			virtual void OnStackStatusChange(STACK_STATUS new_status);			
			//virtual void OnDataReceived (void *p_data, short len);
			void OnClientStateChange(BD_ADDR bda, DEV_CLASS dev_class, BD_NAME name, short com_port, SPP_STATE_CODE state);
			
			//char data[4096];
			BOOL InquiryEventComplete;
			short bt_stack_status;
			short comPort;
			int bt_counter;
			wchar_t bt_devices[256][BLUETOOTH_MAX_NAME_SIZE];
			UINT8 bt_addresses[256][BD_ADDR_LEN];		
	           




		};


