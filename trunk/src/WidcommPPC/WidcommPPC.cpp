// WidcommPPC.cpp : Defines the initialization routines for the DLL.
//

#include "stdafx.h"
#include "WidcommPPC.h"

#ifdef _DEBUG
#define new DEBUG_NEW
#endif

 WidcommStackPPC::WidcommStackPPC()
{
}

 WidcommStackPPC::~WidcommStackPPC()
{
    WIDCOMMSDK_ShutDown();
}
/*void  WidcommStackPPC::OnDataReceived (void *p_data, short len)
 {
 }*/
void  WidcommStackPPC::OnDeviceResponded(BD_ADDR bda, DEV_CLASS devClass, BD_NAME bdName, BOOL bConnected)
{
  //check if we already have listed this device address
  int i = 0;
  bool exists = false;
  while(i < 256 && !exists)
  {
    if(memcmp(bt_addresses[i], bda, BD_ADDR_LEN) == 0)
      exists = true;
    i++;
  }

  if(strlen((const char*)bdName) > 0 && !exists)
  {
    MultiByteToWideChar(CP_ACP, 0, (const char*)bdName, BD_NAME_LEN, bt_devices[bt_counter], BD_NAME_LEN);
    memcpy(bt_addresses[bt_counter], bda, BD_ADDR_LEN); 
    bt_counter++;
  }
}

void  WidcommStackPPC::OnStackStatusChange(STACK_STATUS new_status)
{
   switch (new_status)
    {
    case CBtIf::DEVST_DOWN:
        {
           bt_stack_status = 1;
        }
        break;
    case CBtIf::DEVST_ERROR:        // no longer used, but could come from older stacks
        {
           bt_stack_status = 2;
        }
        break;
        
    case CBtIf::DEVST_UNLOADED:
        {
           bt_stack_status = 3;
        }
        break;

    case CBtIf::DEVST_RELOADED:
        {
           bt_stack_status = 4;
        }
        break;

    case CBtIf::DEVST_UP:           // no longer used, but could come from older stacks
        {
           bt_stack_status = 5;
        }
        break;
    }
}

void  WidcommStackPPC::OnInquiryComplete(BOOL bSuccess, short nResponses)
{
	// Notify that the results have been set
	InquiryEventComplete = TRUE;	
}

void  WidcommStackPPC::OnClientStateChange(BD_ADDR bda, DEV_CLASS dev_class, BD_NAME name, short com_port, SPP_STATE_CODE state)
{
  //pure virtual function has to be implemented !!!
  if (state == SPP_CONNECTED)
  {
    comPort = com_port;
  }
  else
  {
    comPort = -1;
  }
}