

#include "WidcommPPC.h"



#define WMAPI __declspec(dllexport)

extern "C" {

WMAPI void* __stdcall CreateWidcommStack();
WMAPI BOOL __stdcall DeleteWidcommStack(void* wdStack);
WMAPI BOOL __stdcall StartInquiry(void* wdStack);
WMAPI void __stdcall StopInquiry(void* wdStack);
WMAPI BOOL __stdcall InquiryCompleteEvent(void* wdStack, int* device_index);
WMAPI BOOL __stdcall SetAutoReconnect(void* wdStack);

WMAPI short __stdcall GetStackStatus(void* wdStack);

WMAPI BOOL __stdcall IsStackServerUp(void* wdStack);
WMAPI BOOL __stdcall IsDeviceReady(void* wdStack);

//Spp
WMAPI int __stdcall SppCreateConnection(void* wdStack, UINT8 scn, ULONGLONG p_bda);
WMAPI int __stdcall SppRemoveConnection(void* wdStack);
WMAPI short __stdcall SppComPort(void* wdStack);

WMAPI wchar_t* __stdcall DeviceResponded(void* wdStack, ULONGLONG* adr, ULONGLONG device_index);

};



