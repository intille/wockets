// Test.cpp : Defines the entry point for the console application.
//

#include "stdafx.h"
#include <windows.h>
#include <commctrl.h>
#include <winsock2.h> 
#include <ws2bth.h>
#include <bt_sdp.h>
#include <bthapi.h>
#include <bt_api.h>

 
#define BUF_MAX 256 
 
int IsRfcommUuid(NodeData *pNode)
{
   if (pNode->type != SDP_TYPE_UUID)
      return FALSE;

   if (pNode->specificType      == SDP_ST_UUID16)
      return (pNode->u.uuid16   == RFCOMM_PROTOCOL_UUID16);
   else if (pNode->specificType == SDP_ST_UUID32)
      return (pNode->u.uuid32   == RFCOMM_PROTOCOL_UUID16);
   else if (pNode->specificType == SDP_ST_UUID128)
      return (0 == memcmp(&RFCOMM_PROTOCOL_UUID,&pNode->
              u.uuid128,sizeof(GUID)));

   return FALSE;
}

HRESULT FindRFCOMMChannel (unsigned char *pStream, int cStream,
                           unsigned char* nChannel)
{
   ISdpRecord **pRecordArg = NULL;
   int cRecordArg          = 0;
   ISdpStream *pIStream    = NULL;
   HRESULT hr              = 0;
   ULONG ulError           = 0;

   nChannel = 0;

   hr = CoCreateInstance(__uuidof(SdpStream),NULL,
                         CLSCTX_INPROC_SERVER,
                         __uuidof(ISdpStream),(LPVOID *)
                         &pIStream);

   if ( FAILED(hr) || pIStream == NULL )
      return hr;

   hr = pIStream->Validate (pStream, cStream,&ulError);

   if (SUCCEEDED(hr))
   {
      hr = pIStream->VerifySequenceOf(pStream, cStream,
                                      SDP_TYPE_SEQUENCE,NULL,
                                      (ULONG *)&cRecordArg);

      if (SUCCEEDED(hr) && cRecordArg > 0)
      {
         pRecordArg =
            (ISdpRecord **) CoTaskMemAlloc(sizeof(ISdpRecord*)
                                           * cRecordArg);

         if (pRecordArg != NULL)
         {
            hr =
               pIStream->RetrieveRecords(pStream, cStream,
                                         pRecordArg,(ULONG *)
                                         &cRecordArg);

            if ( FAILED(hr) )
            {
               CoTaskMemFree(pRecordArg);
               pRecordArg = NULL;
               cRecordArg = 0;
            }
         }
         else
         {
            hr = E_OUTOFMEMORY;
         }
     }
   }

   if (pIStream != NULL)
   {
      pIStream->Release();
      pIStream = NULL;
   }

   if ( FAILED(hr) )
      return hr;

   for (int i = 0; (nChannel == 0) && (i < cRecordArg); i++)
   {
      ISdpRecord *pRecord = pRecordArg[i];
      // contains SDP_ATTRIB_PROTOCOL_DESCRIPTOR_LIST data,
      // if available
      NodeData protocolList;

      if (ERROR_SUCCESS !=
          pRecord->GetAttribute(SDP_ATTRIB_PROTOCOL_DESCRIPTOR_LIST,
                                &protocolList) ||
                                (protocolList.type !=
                                 SDP_TYPE_CONTAINER))
      {
         if (protocolList.type == SDP_TYPE_STRING)
            CoTaskMemFree(protocolList.u.str.val);
         else if (protocolList.type == SDP_TYPE_URL)
            CoTaskMemFree(protocolList.u.url.val);
         continue;
      }

      ISdpNodeContainer *pRecordContainer = protocolList.u.container;
      int cProtocols = 0;
      NodeData protocolDescriptor;

      pRecordContainer->GetNodeCount((DWORD *)&cProtocols);
      for (int j = 0; (nChannel == 0) && (j < cProtocols); j++)
      {
         pRecordContainer->GetNode(j,&protocolDescriptor);

         if (protocolDescriptor.type != SDP_TYPE_CONTAINER)
            continue;

         ISdpNodeContainer *pProtocolContainer =
            protocolDescriptor.u.container;
         int cProtocolAtoms = 0;
         pProtocolContainer->GetNodeCount((DWORD *)&cProtocolAtoms);

         for (int k = 0; (nChannel == 0) && (k < cProtocolAtoms); k++)
         {
            NodeData nodeAtom;
            pProtocolContainer->GetNode(k,&nodeAtom);

            if (IsRfcommUuid(&nodeAtom))
            {
               if (k+1 == cProtocolAtoms)
               {
                  // Error: Channel ID should follow RFCOMM uuid
                  break;
               }

               NodeData channelID;
               pProtocolContainer->GetNode(k+1,&channelID);

               switch(channelID.specificType)
               {
               case SDP_ST_UINT8:
                  *nChannel = channelID.u.int8;
                  break;
               case SDP_ST_INT8:
                  *nChannel = channelID.u.int8;
                  break;
               case SDP_ST_UINT16:
                  *nChannel = channelID.u.uint16;
                  break;
               case SDP_ST_INT16:
                  *nChannel = channelID.u.int16;
                  break;
               case SDP_ST_UINT32:
                  *nChannel = channelID.u.uint32;
                  break;
               case SDP_ST_INT32:
                  *nChannel = channelID.u.int32;
                  break;
               default:
                  *nChannel = 0;
               }
               break;
            }
         }
      }
      if (protocolList.type == SDP_TYPE_STRING)
         CoTaskMemFree(protocolList.u.str.val);
      else if (protocolList.type == SDP_TYPE_URL)
         CoTaskMemFree(protocolList.u.url.val);
   }

   // cleanup
   for (int i = 0; i < cRecordArg; i++)
	   pRecordArg[i]->Release();
   CoTaskMemFree(pRecordArg);

   return (nChannel != 0) ? S_OK : S_FALSE;
}

int GetDI (WCHAR **pp, unsigned int *pi) { 
	while (**pp == ' ') 
		++*pp; 
 
	int iDig = 0; 
	*pi = 0; 
	while (iswdigit (**pp)) { 
		int c = **pp; 
 
		c = c - '0'; 
 
		if ((c < 0) || (c > 9)) 
			return FALSE; 
 
		*pi = *pi * 10 + c; 
 
		++*pp; 
 
		++iDig; 
	} 
 
	if ((iDig <= 0) || (iDig > 10)) 
		return FALSE; 
 
	return TRUE; 
} 
 
int GetBA (WCHAR **pp, BT_ADDR *pba) { 
	while (**pp == ' ') 
		++*pp; 
 
	for (int i = 0 ; i < 4 ; ++i, ++*pp) { 
		if (! iswxdigit (**pp)) 
			return FALSE; 
 
		int c = **pp; 
		if (c >= 'a') 
			c = c - 'a' + 0xa; 
		else if (c >= 'A') 
			c = c - 'A' + 0xa; 
		else c = c - '0'; 
 
		if ((c < 0) || (c > 16)) 
			return FALSE; 
 
		*pba = *pba * 16 + c; 
	} 
 
	for (int i = 0 ; i < 8 ; ++i, ++*pp) { 
		if (! iswxdigit (**pp)) 
			return FALSE; 
 
		int c = **pp; 
		if (c >= 'a') 
			c = c - 'a' + 0xa; 
		else if (c >= 'A') 
			c = c - 'A' + 0xa; 
		else c = c - '0'; 
 
		if ((c < 0) || (c > 16)) 
			return FALSE; 
 
		*pba = *pba * 16 + c; 
	} 
 
	if ((**pp != ' ') && (**pp != '\0')) 
		return FALSE; 
 
	return TRUE; 
} 
 
#define GUID_FORMAT     L"%08x-%04x-%04x-%02x%02x-%02x%02x%02x%02x%02x%02x\n" 
#define GUID_ELEMENTS(p) &p->Data1, &p->Data2, &p->Data3,&p->Data4[0], &p->Data4[1], &p->Data4[2], &p->Data4[3],&p->Data4[4], &p->Data4[5], &p->Data4[6], &p->Data4[7] 
 
 
int GetGUID(WCHAR *psz, GUID *pGUID) { 
	return (11 ==  swscanf(psz,GUID_FORMAT,GUID_ELEMENTS(pGUID))); 
} 
 
#define BPR		8 
 
int GetUx (WCHAR **pp, void *pRes, int nDigs) { 
	while (**pp == ' ') 
		++*pp; 
	if (**pp != '0') 
		return FALSE; 
	++*pp; 
	if (**pp != 'x') 
		return FALSE; 
 
	++*pp; 
 
	int iDig = 0; 
	int iRes = 0; 
	while (iswxdigit (**pp)) { 
		int c = **pp; 
		if (c >= 'a') 
			c = c - 'a' + 0xa; 
		else if (c >= 'A') 
			c = c - 'A' + 0xa; 
		else c = c - '0'; 
 
		if ((c < 0) || (c > 16)) 
			return FALSE; 
 
		iRes = iRes * 16 + c; 
 
		++*pp; 
 
		++iDig; 
	} 
 
	if (iDig > nDigs) 
		return FALSE; 
 
	switch (nDigs) { 
	case 2: 
		*(unsigned char *)pRes = (unsigned char)iRes; 
		break; 
	case 4: 
		*(unsigned short *)pRes = (unsigned short)iRes; 
		break; 
	case 8: 
		*(unsigned int *)pRes = (unsigned int)iRes; 
		break; 
	} 
 
	return TRUE; 
} 
 
void DumpBuff (WCHAR *szLineHeader, unsigned char *lpBuffer, unsigned int cBuffer) { 
	WCHAR szLine[5 + 7 + 2 + 4 * BPR]; 
 
	for (int i = 0 ; i < (int)cBuffer ; i += BPR) { 
		int bpr = cBuffer - i; 
		if (bpr > BPR) 
			bpr = BPR; 
 
		wsprintf (szLine, L"%04x ", i); 
		WCHAR *p = szLine + wcslen (szLine); 
 
		int j = 0;
		for ( ; j < bpr ; ++j) { 
			WCHAR c = (lpBuffer[i + j] >> 4) & 0xf; 
			if (c > 9) c += L'a' - 10; else c += L'0'; 
			*p++ = c; 
			c = lpBuffer[i + j] & 0xf; 
			if (c > 9) c += L'a' - 10; else c += L'0'; 
			*p++ = c; 
			*p++ = L' '; 
		} 
 
		for ( ; j < BPR ; ++j) { 
			*p++ = L' '; 
			*p++ = L' '; 
			*p++ = L' '; 
		} 
 
		*p++ = L' '; 
		*p++ = L' '; 
		*p++ = L' '; 
		*p++ = L'|'; 
		*p++ = L' '; 
		*p++ = L' '; 
		*p++ = L' '; 
 
		for (j = 0 ; j < bpr ; ++j) { 
			WCHAR c = lpBuffer[i + j]; 
			if ((c < L' ') || (c >= 127)) 
				c = L'.'; 
 
			*p++ = c; 
		} 
 
		for ( ; j < BPR ; ++j) { 
			*p++ = L' '; 
		} 
 
		*p++ = L'\n'; 
		*p++ = L'\0'; 
 
		wprintf (L"%s %s", szLineHeader ? szLineHeader : L"", szLine); 
	} 
} 
 
static void DumpFeatures (unsigned char *pf) { 
	wprintf (L"Supported LMP features:\n"); 
	if ((*pf) & 0x01) 
		wprintf (L"\t3-slot packets\n"); 
	if ((*pf) & 0x02) 
		wprintf (L"\t5-slot packets\n"); 
	if ((*pf) & 0x04) 
		wprintf (L"\tencryption\n"); 
	if ((*pf) & 0x08) 
		wprintf (L"\tslot offset\n"); 
	if ((*pf) & 0x10) 
		wprintf (L"\ttiming accuracy\n"); 
	if ((*pf) & 0x20) 
		wprintf (L"\tswitch\n"); 
	if ((*pf) & 0x40) 
		wprintf (L"\thold\n"); 
	if ((*pf) & 0x80) 
		wprintf (L"\tsniff\n"); 
	++pf; 
	if ((*pf) & 0x01) 
		wprintf (L"\tpark\n"); 
	if ((*pf) & 0x02) 
		wprintf (L"\tRSSI\n"); 
	if ((*pf) & 0x04) 
		wprintf (L"\tchannel-quality driven rate\n"); 
	if ((*pf) & 0x08) 
		wprintf (L"\tSCO\n"); 
	if ((*pf) & 0x10) 
		wprintf (L"\tHV2\n"); 
	if ((*pf) & 0x20) 
		wprintf (L"\tHV3\n"); 
	if ((*pf) & 0x40) 
		wprintf (L"\tu-law log\n"); 
	if ((*pf) & 0x80) 
		wprintf (L"\ta-law log\n"); 
	++pf; 
	if ((*pf) & 0x01) 
		wprintf (L"\tCVSD\n"); 
	if ((*pf) & 0x02) 
		wprintf (L"\tpaging scheme\n"); 
	if ((*pf) & 0x04) 
		wprintf (L"\tpower control\n"); 
	if ((*pf) & 0x08) 
		wprintf (L"\ttransparent SCO data\n"); 
	if ((*pf) & 0x10) 
		wprintf (L"\tflow lag bit 0\n"); 
	if ((*pf) & 0x20) 
		wprintf (L"\tflow lag bit 0\n"); 
	if ((*pf) & 0x40) 
		wprintf (L"\tflow lag bit 0\n"); 
} 
 
DWORD WINAPI ReadThread (LPVOID lpVoid) { 
	wprintf (L"Reader thread started for socket 0x%08x\n", lpVoid); 
	SOCKET s = (SOCKET)lpVoid; 
	WCHAR szHeader[25]; 
 
	SOCKADDR_BTH sa; 
	int size = sizeof(sa); 
 
	if (0 == getsockname (s, (SOCKADDR *)&sa, &size)) { 
		if (size != sizeof(sa)) { 
			wprintf (L"getsockname returned incorrect size (%d, expected %d)\n", size, sizeof(sa)); 
			wcscpy (szHeader, L">>>>"); 
		} else { 
			wsprintf (szHeader, L"%04x%08x 0x%02 >", GET_NAP(sa.btAddr),  
					GET_SAP(sa.btAddr), sa.port); 
		} 
	} else { 
		wprintf (L"getsockname failed. Error = %d\n", WSAGetLastError ()); 
		wcscpy (szHeader, L">>>>"); 
	} 
 
	for ( ; ; ) { 
		char buffer[BUF_MAX]; 
		int len = recv (s, buffer, sizeof(buffer), 0); 
		if (len <= 0) 
			break; 
 
		DumpBuff (szHeader, (unsigned char *)buffer, len); 
	} 
 
	closesocket (s); 
 
	wprintf (L"Reader thread ended for socket 0x%08x\n", lpVoid); 
 
	return 0; 
} 
 
static void Help (void) { 
	wprintf (L"Use one of:\n\tEXIT\n\tSEND file\n\tTEXT string\n\tBIN binary data (list of 2 dig hex numbers)\n"); 
	wprintf (L"\tAUTH\n\tENCRYPT {on, off}\n\tPIN binary data (list of 2 dig hex numbers)\n\tMSC xx xx\n\tRLS xx\n"); 
	wprintf (L"\tXON dec number\n\tXOFF dec number\n\tSENDBUFF dec number\n\tRECVBUFF dec number\n\tGETALL\n\tGETVERSION\n"); 
	wprintf (L"\tHOLD xxxx xxxx\n\tSNIFF xxxx xxxx xxxx xxxx\n\t\n\tUNSNIFF\n\tPARK xxxx xxxx\n\tUNPARK\n"); 
	wprintf (L"\tGETMODE\n\tGETPOLICY\n\tSETPOLICY xxxx\n"); 
} 
 
DWORD WINAPI WriteThread (LPVOID lpVoid) { 
	wprintf (L"Writer thread started for socket 0x%08x\n", lpVoid); 
 
	Help (); 
 
	SOCKET s = (SOCKET)lpVoid; 
 
	for ( ; ; ) { 
		wprintf (L"> "); 
		WCHAR szCommand[BUF_MAX]; 
		if (! fgetws (szCommand, BUF_MAX, stdin)) 
			break; 
 
		WCHAR *szEOL = wcschr (szCommand, L'\n'); 
		if (szEOL) 
			*szEOL = '\0'; 
 
		if (wcsicmp (szCommand, L"EXIT") == 0) 
			break; 
 
		if (wcsicmp (szCommand, L"GETALL") == 0) { 
			union { 
				int i; 
				BTH_SOCKOPT_SECURITY bs; 
				int iarr[2]; 
			}; 
 
			int iRes; 
			int ilen = sizeof(bs); 
			bs.iLength = 16; 
			bs.btAddr  = 0; 
 
			iRes = getsockopt (s, SOL_RFCOMM, SO_BTH_GET_LINK, (char *)&bs, &ilen); 
			if (iRes) 
				wprintf (L"SO_BTH_GET_LINK : error %d\n", iRes); 
			else { 
				unsigned char *arr = bs.caData; 
				wprintf (L"SO_BTH_GET_LINK : key %02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x\n", 
					arr[0], arr[1], arr[2], arr[3], arr[4], arr[5], arr[6], arr[7], 
					arr[8], arr[9], arr[10], arr[11], arr[12], arr[13], arr[14], arr[15]); 
			} 
 
			ilen = sizeof(i); 
			iRes = getsockopt (s, SOL_RFCOMM, SO_BTH_GET_MTU, (char *)&i, &ilen); 
			if (iRes) 
				wprintf (L"SO_BTH_GET_MTU : error %d\n", iRes); 
			else 
				wprintf (L"SO_BTH_GET_MTU : mtu %d\n", i); 
 
			ilen = sizeof(i); 
			iRes = getsockopt (s, SOL_RFCOMM, SO_BTH_GET_MTU_MAX, (char *)&i, &ilen); 
			if (iRes) 
				wprintf (L"SO_BTH_GET_MTU_MAX : error %d\n", iRes); 
			else 
				wprintf (L"SO_BTH_GET_MTU_MAX : max mtu %d\n", i); 
 
			ilen = sizeof(i); 
			iRes = getsockopt (s, SOL_RFCOMM, SO_BTH_GET_MTU_MIN, (char *)&i, &ilen); 
			if (iRes) 
				wprintf (L"SO_BTH_GET_MTU_MIN : error %d\n", iRes); 
			else 
				wprintf (L"SO_BTH_GET_MTU_MIN : min mtu %d\n", i); 
 
			ilen = sizeof(i); 
			iRes = getsockopt (s, SOL_RFCOMM, SO_BTH_GET_XON_LIM, (char *)&i, &ilen); 
			if (iRes) 
				wprintf (L"SO_BTH_GET_XON_LIM : error %d\n", iRes); 
			else 
				wprintf (L"SO_BTH_GET_XON_LIM : xon %d\n", i); 
 
			ilen = sizeof(i); 
			iRes = getsockopt (s, SOL_RFCOMM, SO_BTH_GET_XOFF_LIM, (char *)&i, &ilen); 
			if (iRes) 
				wprintf (L"SO_BTH_GET_XOFF_LIM : error %d\n", iRes); 
			else 
				wprintf (L"SO_BTH_GET_XOFF_LIM : xoff %d\n", i); 
 
			ilen = sizeof(i); 
			iRes = getsockopt (s, SOL_RFCOMM, SO_BTH_GET_SEND_BUFFER, (char *)&i, &ilen); 
			if (iRes) 
				wprintf (L"SO_BTH_GET_SEND_BUFFER : error %d\n", iRes); 
			else 
				wprintf (L"SO_BTH_GET_SEND_BUFFER : send buf %d\n", i); 
 
			ilen = sizeof(i); 
			iRes = getsockopt (s, SOL_RFCOMM, SO_BTH_GET_RECV_BUFFER, (char *)&i, &ilen); 
			if (iRes) 
				wprintf (L"SO_BTH_GET_RECV_BUFFER : error %d\n", iRes); 
			else 
				wprintf (L"SO_BTH_GET_RECV_BUFFER : recv buf %d\n", i); 
 
			ilen = sizeof(iarr); 
			iRes = getsockopt (s, SOL_RFCOMM, SO_BTH_GET_V24_BR, (char *)iarr, &ilen); 
			if (iRes) 
				wprintf (L"SO_BTH_GET_V24_BR : error %d\n", iRes); 
			else 
				wprintf (L"SO_BTH_GET_V24_BR : v24 %d br %d\n", iarr[0], iarr[1]); 
 
			ilen = sizeof(i); 
			iRes = getsockopt (s, SOL_RFCOMM, SO_BTH_GET_RLS, (char *)&i, &ilen); 
			if (iRes) 
				wprintf (L"SO_BTH_GET_RLS : error %d\n", iRes); 
			else 
				wprintf (L"SO_BTH_GET_RLS : v24 %d\n", i); 
 
			ilen = sizeof(i); 
			iRes = getsockopt (s, SOL_RFCOMM, SO_BTH_GET_FLOW_TYPE, (char *)&i, &ilen); 
			if (iRes) 
				wprintf (L"SO_BTH_GET_FLOW_TYPE : error %d\n", iRes); 
			else 
				wprintf (L"SO_BTH_GET_FLOW_TYPE : flow %s\n", i == 0 ? L"NOT CREDIT" : ((i == 1) ? L"CREDIT" : L"UNKNOWN")); 
 
			continue; 
		} 
 
		if (wcsicmp (szCommand, L"AUTH") == 0) { 
			int empty = 0; 
			wprintf (L"setsockopt returns %d\n", 
				setsockopt (s, SOL_RFCOMM, SO_BTH_AUTHENTICATE, (char *)0, sizeof(empty))); 
			continue; 
		} 
 
		if (wcsicmp (szCommand, L"ENCRYPT ON") == 0) { 
			int e = TRUE; 
			wprintf (L"setsockopt returns %d\n", 
				setsockopt (s, SOL_RFCOMM, SO_BTH_ENCRYPT, (char *)&e, sizeof(e))); 
			continue; 
		} 
 
		if (wcsicmp (szCommand, L"ENCRYPT OFF") == 0) { 
			int e = FALSE; 
			wprintf (L"setsockopt returns %d\n", 
				setsockopt (s, SOL_RFCOMM, SO_BTH_ENCRYPT, (char *)&e, sizeof(e))); 
			continue; 
		} 
 
		if (wcsicmp (szCommand, L"GETMODE") == 0) { 
			int mode = -1; 
			int isize = sizeof(mode); 
			wprintf (L"getsockopt returns %d\n", 
					getsockopt (s, SOL_RFCOMM, SO_BTH_GET_MODE, (char *)&mode, &isize)); 
			wprintf (L"mode = %d (%s)\n", mode, (mode == 0 ? L"active" : (mode == 1 ? L"hold" : (mode == 2 ? L"sniff" : (mode == 3 ? L"park" : L"???"))))); 
 
			continue; 
		} 
 
		if (wcsicmp (szCommand, L"GETPOLICY") == 0) { 
			int policy = -1; 
			int isize = sizeof(policy); 
			wprintf (L"getsockopt returns %d\n", 
					getsockopt (s, SOL_RFCOMM, SO_BTH_GET_LINK_POLICY, (char *)&policy, &isize)); 
			wprintf (L"policy = %d (%s %s %s %s)\n", policy, policy & 1 ? L"master-slave" : L"", 
				policy & 2 ? L"hold" : L"", policy & 4 ? L"sniff" : L"", policy & 8 ? L"park" : L""); 
 
			continue; 
		} 
 
		if (wcsnicmp (szCommand, L"SETPOLICY ", 10) == 0) { 
			WCHAR *szData = szCommand + 10; 
 
			unsigned short policy; 
 
			if (! GetUx (&szData, &policy, 4)) { 
				wprintf (L"Syntax: policy\n"); 
				continue; 
			} 
 
 
			unsigned int ipolicy = policy; 
 
			wprintf (L"setsockopt returns %d\n", 
					setsockopt (s, SOL_RFCOMM, SO_BTH_SET_LINK_POLICY, (char *)&ipolicy, sizeof(ipolicy))); 
			continue; 
		} 
 
 
		if (wcsnicmp (szCommand, L"PARK ", 5) == 0) { 
			WCHAR *szData = szCommand + 5; 
 
			BTH_PARK_MODE pm; 
 
			if (! GetUx (&szData, &pm.beacon_max, 4)) { 
				wprintf (L"Syntax: beacon_max\n"); 
				continue; 
			} 
 
			if (! GetUx (&szData, &pm.beacon_min, 4)) { 
				wprintf (L"Syntax: beacon_min\n"); 
				continue; 
			} 
 
			pm.interval = 0; 
 
			wprintf (L"setsockopt returns %d\n", 
					setsockopt (s, SOL_RFCOMM, SO_BTH_ENTER_PARK_MODE, (char *)&pm, sizeof(pm))); 
			wprintf (L"interval = %d\n", pm.interval); 
			continue; 
		} 
 
		if (wcsicmp (szCommand, L"UNPARK") == 0) { 
			int iIgnore = 0; 
			wprintf (L"setsockopt returns %d\n", 
					setsockopt (s, SOL_RFCOMM, SO_BTH_EXIT_PARK_MODE, (char *)&iIgnore, sizeof(iIgnore))); 
			continue; 
		} 
 
		if (wcsnicmp (szCommand, L"HOLD ", 5) == 0) { 
			WCHAR *szData = szCommand + 5; 
 
			BTH_HOLD_MODE hm; 
 
			if (! GetUx (&szData, &hm.hold_mode_max, 4)) { 
				wprintf (L"Syntax: hold_mode_max\n"); 
				continue; 
			} 
 
			if (! GetUx (&szData, &hm.hold_mode_min, 4)) { 
				wprintf (L"Syntax: hold_mode_min\n"); 
				continue; 
			} 
 
			hm.interval = 0; 
 
			wprintf (L"setsockopt returns %d\n", 
					setsockopt (s, SOL_RFCOMM, SO_BTH_ENTER_HOLD_MODE, (char *)&hm, sizeof(hm))); 
			wprintf (L"interval = %d\n", hm.interval); 
			continue; 
		} 
 
		if (wcsnicmp (szCommand, L"SNIFF ", 6) == 0) { 
			WCHAR *szData = szCommand + 6; 
 
			int c = 0; 
			BTH_SNIFF_MODE sm; 
 
			if (! GetUx (&szData, &sm.sniff_mode_max, 4)) { 
				wprintf (L"Syntax: sniff_mode_max\n"); 
				continue; 
			} 
 
			if (! GetUx (&szData, &sm.sniff_mode_min, 4)) { 
				wprintf (L"Syntax: sniff_mode_min\n"); 
				continue; 
			} 
 
			if (! GetUx (&szData, &sm.sniff_attempt, 4)) { 
				wprintf (L"Syntax: sniff_attempt\n"); 
				continue; 
			} 
 
			if (! GetUx (&szData, &sm.sniff_timeout, 4)) { 
				wprintf (L"Syntax: sniff_timeout\n"); 
				continue; 
			} 
 

			sm.interval = 0; 
 
			wprintf (L"setsockopt returns %d\n", 
					setsockopt (s, SOL_RFCOMM, SO_BTH_ENTER_SNIFF_MODE, (char *)&sm, sizeof(sm))); 
			wprintf (L"interval = %d\n", sm.interval); 
			continue; 
		} 
 
		if (wcsicmp (szCommand, L"UNSNIFF") == 0) { 
			int iIgnore = 0; 
			wprintf (L"setsockopt returns %d\n", 
					setsockopt (s, SOL_RFCOMM, SO_BTH_EXIT_SNIFF_MODE, (char *)&iIgnore, sizeof(iIgnore))); 
			continue; 
		} 
 
		if (wcsnicmp (szCommand, L"PIN ", 4) == 0) { 
			WCHAR *szData = szCommand + 4; 
 
			int c = 0; 
			BTH_SOCKOPT_SECURITY bs; 
			unsigned char *b = (unsigned char *)bs.caData; 
 
			for ( ; ; ) { 
				if (! GetUx (&szData, b + c, 2)) 
					break; 
 
				++c; 
			} 
 
			bs.iLength = c; 
			bs.btAddr  = 0; 
 
			if (c > 0) { 
				wprintf (L"setsockopt returns %d\n", 
					setsockopt (s, SOL_RFCOMM, SO_BTH_SET_PIN, (char *)&bs, sizeof(bs))); 
			} else 
				wprintf (L"Empty string!\n"); 
 
			continue; 
		} 
 
		if (wcsnicmp (szCommand, L"MSC ", 4) == 0) { 
			WCHAR *p = szCommand + 4; 
 
			int x[2]; 
			if (! GetUx (&p, &x[0], 8)) { 
				wprintf (L"v24 ???\n"); 
				continue; 
			} 
 
			if (! GetUx (&p, &x[1], 8)) { 
				wprintf (L"br ???\n"); 
				continue; 
			} 
 
			wprintf (L"setsockopt returns %d\n", 
					setsockopt (s, SOL_RFCOMM, SO_BTH_SEND_MSC, (char *)x, sizeof(x))); 
			continue; 
		} 
 
		if (wcsnicmp (szCommand, L"RLS ", 4) == 0) { 
			WCHAR *p = szCommand + 4; 
 
			int x; 
			if (! GetUx (&p, &x, 8)) { 
				wprintf (L"rls ???\n"); 
				continue; 
			} 
 
			wprintf (L"setsockopt returns %d\n", 
					setsockopt (s, SOL_RFCOMM, SO_BTH_SEND_RLS, (char *)&x, sizeof(int))); 
			continue; 
		} 
 
		if (wcsnicmp (szCommand, L"XON ", 4) == 0) { 
			WCHAR *p = szCommand + 4; 
 
			unsigned int x; 
			if (! GetDI (&p, &x)) { 
				wprintf (L"rls ???\n"); 
				continue; 
			} 
 
			wprintf (L"setsockopt returns %d\n", 
					setsockopt (s, SOL_RFCOMM, SO_BTH_SET_XON_LIM, (char *)&x, sizeof(int))); 
			continue; 
		} 
 
		if (wcsnicmp (szCommand, L"XOFF ", 5) == 0) { 
			WCHAR *p = szCommand + 5; 
 
			unsigned int x; 
			if (! GetDI (&p, &x)) { 
				wprintf (L"rls ???\n"); 
				continue; 
			} 
 
			wprintf (L"setsockopt returns %d\n", 
					setsockopt (s, SOL_RFCOMM, SO_BTH_SET_XOFF_LIM, (char *)&x, sizeof(int))); 
			continue; 
		} 
 
		if (wcsnicmp (szCommand, L"SENDBUFF ", 9) == 0) { 
			WCHAR *p = szCommand + 9; 
 
			unsigned int x; 
			if (! GetDI (&p, &x)) { 
				wprintf (L"rls ???\n"); 
				continue; 
			} 
 
			wprintf (L"setsockopt returns %d\n", 
					setsockopt (s, SOL_RFCOMM, SO_BTH_SET_SEND_BUFFER, (char *)&x, sizeof(int))); 
			continue; 
		} 
 
		if (wcsnicmp (szCommand, L"RECVBUFF ", 9) == 0) { 
			WCHAR *p = szCommand + 9; 
 
			unsigned int x; 
			if (! GetDI (&p, &x)) { 
				wprintf (L"rls ???\n"); 
				continue; 
			} 
 
			wprintf (L"setsockopt returns %d\n", 
					setsockopt (s, SOL_RFCOMM, SO_BTH_SET_RECV_BUFFER, (char *)&x, sizeof(int))); 
			continue; 
		} 
 
		if (wcsnicmp (szCommand, L"SEND ", 5) == 0) { 
			WCHAR *szName = szCommand + 5; 
 
			FILE *fp = _wfopen (szName, L"r"); 
			if (fp) { 
				unsigned char b[BUF_MAX]; 
				for ( ; ; ) { 
					int c = fread (b, 1, sizeof(b), fp); 
					if (c <= 0) 
						break; 
 
					int x = send (s, (char *)b, c, 0); 
					if (x != c) { 
						wprintf (L"send returns %d, Error = %d\n", x, WSAGetLastError ()); 
						break; 
					} 
				} 
 
				fclose (fp); 
			} else 
				wprintf (L"Cannot open %s\n", szCommand); 
 
			continue; 
		} 
 
		if (wcsnicmp (szCommand, L"TEXT ", 5) == 0) { 
			WCHAR *szString = szCommand + 5; 
			int c = (wcslen (szString) + 1) * sizeof(WCHAR); 
			if (c > sizeof (WCHAR)) { 
				int x = send (s, (char *)szString, c, 0); 
				if (x != c) 
					wprintf (L"send returns %d, Error = %d\n", x, WSAGetLastError ()); 
			} else 
				wprintf (L"Empty string!\n"); 
 
			continue; 
		} 
 
		if (wcsnicmp (szCommand, L"BIN ", 4) == 0) { 
			WCHAR *szData = szCommand + 4; 
 
			int c = 0; 
			unsigned char *b = (unsigned char *)szCommand; 
 
			for ( ; ; ) { 
				if (! GetUx (&szData, b + c, 2)) 
					break; 
 
				++c; 
			} 
 
			if (c > 0) { 
				int x = send (s, (char *)b, c, 0); 
				if (x != c) 
					wprintf (L"send returns %d, Error = %d\n", x, WSAGetLastError ()); 
			} else 
				wprintf (L"Empty string!\n"); 
 
			continue; 
		} 
 
		if (wcsicmp (szCommand, L"GETVERSION") == 0) { 
			BTH_REMOTE_VERSION bv; 
 
			int iRes; 
			int ilen = sizeof(bv); 
 
			iRes = getsockopt (s, SOL_RFCOMM, SO_BTH_GET_REMOTE_VER, (char *)&bv, &ilen); 
			if (iRes) 
				wprintf (L"SO_BTH_GET_LOCAL_VER : error %d\n", iRes); 
			else { 
				wprintf (L"lmp version %d\n", bv.lmp_version); 
				wprintf (L"lmp revision %d\n", bv.lmp_subversion); 
				wprintf (L"manufacturer: "); 
				switch (bv.manufacturer) { 
				case 0: 
					wprintf (L"Ericsson\n"); 
					break; 
				case 1: 
					wprintf (L"Nokia\n"); 
					break; 
				case 2: 
					wprintf (L"Intel\n"); 
					break; 
				case 3: 
					wprintf (L"IBM\n"); 
					break; 
				case 4: 
					wprintf (L"Toshiba\n"); 
					break; 
				case 5: 
					wprintf (L"3COM\n"); 
					break; 
				case 6: 
					wprintf (L"Microsoft\n"); 
					break; 
				case 7: 
					wprintf (L"Lucent\n"); 
					break; 
				case 8: 
					wprintf (L"Motorola\n"); 
					break; 
				case 9: 
					wprintf (L"Infineon\n"); 
					break; 
				case 10: 
					wprintf (L"CSR\n"); 
					break; 
				case 11: 
					wprintf (L"Silicon Wave\n"); 
					break; 
				case 12: 
					wprintf (L"Digianswer\n"); 
					break; 
				default: 
					wprintf (L"Unknown, code %d\n", bv.manufacturer); 
					break; 
				} 
				DumpFeatures (bv.lmp_features); 
 
			} 
 
			continue; 
		} 
 
		wprintf (L"Command not understood...\n"); 
	} 
 
	closesocket (s); 
 
	wprintf (L"Writer thread ended for socket 0x%08x\n", lpVoid); 
	return 0; 
} 
 
int ProcessSockOpts (SOCKET s, WCHAR **argv, int argc) { 
	while (argc > 0) { 
		unsigned int iOpt = 0; 
		int iName = 0; 
		WCHAR *sz = NULL; 
 
		if (wcsicmp (argv[0], L"AUTH") == 0) 
			iName = SO_BTH_AUTHENTICATE; 
		else if (wcsicmp (argv[0], L"ENCRYPT") == 0) 
			iName = SO_BTH_ENCRYPT; 
		else if ((wcsicmp (argv[0], L"MTU") == 0) && (argc > 1) && (sz = argv[1]) && (GetDI (&sz, &iOpt))) 
			iName = SO_BTH_SET_MTU; 
		else if ((wcsicmp (argv[0], L"MTUMIN") == 0) && (argc > 1) && (sz = argv[1]) && (GetDI (&sz, &iOpt))) 
			iName = SO_BTH_SET_MTU_MIN; 
		else if ((wcsicmp (argv[0], L"MTUMAX") == 0) && (argc > 1) && (sz = argv[1]) && (GetDI (&sz, &iOpt))) 
			iName = SO_BTH_SET_MTU_MAX; 
		else if ((wcsicmp (argv[0], L"XON") == 0) && (argc > 1) && (sz = argv[1]) && (GetDI (&sz, &iOpt))) 
			iName = SO_BTH_SET_XON_LIM; 
		else if ((wcsicmp (argv[0], L"XOFF") == 0) && (argc > 1) && (sz = argv[1]) && (GetDI (&sz, &iOpt))) 
			iName = SO_BTH_SET_XOFF_LIM; 
		else if ((wcsicmp (argv[0], L"SENDBUFF") == 0) && (argc > 1) && (sz = argv[1]) && (GetDI (&sz, &iOpt))) 
			iName = SO_BTH_SET_SEND_BUFFER; 
		else if ((wcsicmp (argv[0], L"RECVBUFF") == 0) && (argc > 1) && (sz = argv[1]) && (GetDI (&sz, &iOpt))) 
			iName = SO_BTH_SET_RECV_BUFFER; 
		else if ((wcsicmp (argv[0], L"PIN") == 0) && (argc > 1)) { 
			++argv; 
			--argc; 
 
			BTH_SOCKOPT_SECURITY bs; 
			bs.iLength = 0; 
			bs.btAddr  = 0; 
 
			while ((bs.iLength < 16) && (argc > 0) && (sz = argv[0]) && GetUx (&sz, bs.caData + bs.iLength, 2)) { 
				++bs.iLength; 
				++argv; 
				--argc; 
			} 
 
			int iRes = setsockopt (s, SOL_RFCOMM, SO_BTH_SET_PIN, (char *)&bs, sizeof(bs)); 
			if (iRes != ERROR_SUCCESS) { 
				wprintf (L"setsockopt returns %d for PIN\n", iRes); 
				return FALSE; 
			} 
 
			continue; 
		} else { 
			wprintf (L"Incorrect syntax: %s\n", argv[0]); 
			return FALSE; 
		} 
 
		int iRes = setsockopt (s, SOL_RFCOMM, iName, (char *)&iOpt, sizeof(iOpt)); 
		if (iRes != ERROR_SUCCESS) { 
			wprintf (L"setsockopt returns %d for %s (name = %d, val = %d)\n", iRes, argv[0], iName, iOpt); 
			return FALSE; 
		} 
 
		++argv; 
		--argc; 
 
		if (sz != NULL) { 
			++argv; 
			--argc; 
		} 
	} 
 
	return TRUE; 
} 



int DetectRFCommChannel(BT_ADDR *pbBtAddr)
{
   int iResult = 0;

   BTHNS_RESTRICTIONBLOB RBlob;
   memset (&RBlob, 0, sizeof(RBlob));

   RBlob.type                   = SDP_SERVICE_SEARCH_ATTRIBUTE_REQUEST;
   RBlob.numRange               = 1;
   RBlob.pRange[0].minAttribute = SDP_ATTRIB_PROTOCOL_DESCRIPTOR_LIST;
   RBlob.pRange[0].maxAttribute = SDP_ATTRIB_PROTOCOL_DESCRIPTOR_LIST;
   RBlob.uuids[0].uuidType      = SDP_ST_UUID16;
   RBlob.uuids[0].u.uuid16      = SerialPortServiceClassID_UUID16;

   BLOB blob;
   blob.cbSize    = sizeof(RBlob);
   blob.pBlobData = (BYTE *)&RBlob;

   SOCKADDR_BTH   sa;
   memset (&sa, 0, sizeof(sa));

   *(BT_ADDR *)(&sa.btAddr) = *pbBtAddr;
   sa.addressFamily = AF_BT;

   CSADDR_INFO      csai;
   memset (&csai, 0, sizeof(csai));
   csai.RemoteAddr.lpSockaddr = (sockaddr *)&sa;
   csai.RemoteAddr.iSockaddrLength = sizeof(sa);

   WSAQUERYSET      wsaq;
   memset (&wsaq, 0, sizeof(wsaq));
   wsaq.dwSize      = sizeof(wsaq);
   wsaq.dwNameSpace = NS_BTH;
   wsaq.lpBlob      = &blob;
   wsaq.lpcsaBuffer = &csai;

   HANDLE hLookup;
   int iRet = WSALookupServiceBegin (&wsaq, 0, &hLookup);
   if (ERROR_SUCCESS == iRet)
   {
      CHAR buf[5000];
      LPWSAQUERYSET pwsaResults = (LPWSAQUERYSET) buf;
      DWORD dwSize  = sizeof(buf);

      memset(pwsaResults,0,sizeof(WSAQUERYSET));
      pwsaResults->dwSize      = sizeof(WSAQUERYSET);
      pwsaResults->dwNameSpace = NS_BTH;
      pwsaResults->lpBlob      = NULL;

      iRet = WSALookupServiceNext (hLookup, 0, &dwSize, pwsaResults);
      if (iRet == ERROR_SUCCESS)
      {
         unsigned char cChannel = 0;
         if (ERROR_SUCCESS == FindRFCOMMChannel(
                              pwsaResults->lpBlob->pBlobData,
                              pwsaResults->lpBlob->cbSize,
                              &cChannel))
                              iResult = cChannel;
      }

      WSALookupServiceEnd(hLookup);
   }

   return iResult;
}
int cChannel;
 

int wmain (int argc, WCHAR **argv) { 
	BT_ADDR	b; 
	unsigned int channel = 0; 
	WCHAR *arg2 = argv[2]; 
	WCHAR *arg3 = argv[3]; 
	WCHAR *arg4 = argv[4]; 

	WSAQUERYSET querySet;
HANDLE hLookup;
char buffer[1000];
DWORD bufferlength;
WSAQUERYSET *results;
SOCKADDR_BTH *btaddr;

 
	WSADATA wsd; 
	if (WSAStartup (MAKEWORD(1,0), &wsd)) { 
		wprintf (L"Initialization of socket subsystem failed! Error = %d\n", WSAGetLastError ()); 
		return 0; 
	} 


		b=0x00066601ab3c; //0x3cab01660600;

memset(&querySet, 0, sizeof(querySet));
querySet.dwSize = sizeof(querySet);
querySet.dwNameSpace = NS_BTH;

int BluetoothQuery_DeviceCount = 0;

if (WSALookupServiceBegin(&querySet, LUP_CONTAINERS, &hLookup) == SOCKET_ERROR)
return false;

while (BluetoothQuery_DeviceCount < 20 )
{
	bufferlength = sizeof(buffer);
	memset(buffer, 0, sizeof(buffer));
	results = (WSAQUERYSET *) &buffer;

	if (WSALookupServiceNext(hLookup, LUP_RETURN_NAME|LUP_RETURN_ADDR, &bufferlength, results) == SOCKET_ERROR)
	{
		int result = WSAGetLastError();
		break;
	}

	btaddr = (SOCKADDR_BTH*)results->lpcsaBuffer->RemoteAddr.lpSockaddr;
	//BluetoothQuery_DeviceAddrList[BluetoothQuery_DeviceCount]=btaddr->btAddr;

	/*if (results->lpszServiceInstanceName != NULL)
		wcscpy((TCHAR *)BluetoothQuery_DeviceNameList[BluetoothQuery_DeviceCount],results->lpszServiceInstanceName);
	else
		wcscpy((TCHAR *)BluetoothQuery_DeviceNameList[BluetoothQuery_DeviceCount],L"<unnamed>");
*/
	if (btaddr->btAddr==b)
		break;
	BluetoothQuery_DeviceCount++;
}

WSALookupServiceEnd(hLookup);


 
	SOCKET s = socket (AF_BT, SOCK_STREAM, BTHPROTO_RFCOMM); 
				BTH_LOCAL_VERSION bv; 
 		if (s == INVALID_SOCKET) { 
			wprintf (L"socket failed, error %d\n", WSAGetLastError ()); 
			return 0; 
		} 
  

	channel = 0; 
		SOCKADDR_BTH sa; 
		memset (&sa, 0, sizeof(sa)); 
 

		sa.addressFamily = AF_BT; 
 
		sa.btAddr = btaddr->btAddr;









//		channel=DetectRFCommChannel();
		
		//sa.port=btaddr->port;
		/*
			if (! GetDI(&arg3, &channel)) { 
			wprintf(L"Invalid format for Channel specified\n"); 
			closesocket(s); 
 
			return 0; 
		} */
 

 
		for (int i=1;(i<10);i++){
		sa.port = i & 0xff; 
 
		//wprintf (L"Connecting to %04x%08x 0x%02x\n", GET_NAP(b), GET_SAP(b), channel & 0xff); 
 
		if (connect (s, (SOCKADDR *)&sa, sizeof(sa))) { 
			wprintf (L"Connect failed, error = %d\n", WSAGetLastError ()); 
			//return 0; 
		} else
			break;
		}




			BTH_SNIFF_MODE sm; 
			sm.sniff_mode_max=0xffff;
			sm.sniff_mode_min=0x0001;
			sm.sniff_attempt=100;
			sm.sniff_timeout=100;
			sm.interval = 0; 
 
int errno = WSAGetLastError();
				if(setsockopt(s, SOL_RFCOMM, SO_BTH_ENTER_SNIFF_MODE, (char *)&sm, sizeof(sm))!=0){

						int errno = WSAGetLastError();
						errno=0;
				}
			wprintf (L"interval = %d\n", sm.interval); 




				int iRes; 
				int ilen = sizeof(bv); 
 
				iRes = getsockopt (s, SOL_RFCOMM, SO_BTH_GET_LOCAL_VER, (char *)&bv, &ilen); 
				if (iRes) 
					wprintf (L"SO_BTH_GET_LOCAL_VER : error %d\n", iRes); 
				else { 
					wprintf (L"hci version %d\n", bv.hci_version); 
					wprintf (L"hci revision %d\n", bv.hci_revision); 
					wprintf (L"lmp version %d\n", bv.lmp_version); 
					wprintf (L"lmp revision %d\n", bv.lmp_subversion); 
					wprintf (L"manufacturer: "); 
					switch (bv.manufacturer) { 
					case 0: 
						wprintf (L"Ericsson\n"); 
						break; 
					case 1: 
						wprintf (L"Nokia\n"); 
						break; 
					case 2: 
						wprintf (L"Intel\n"); 
						break; 
					case 3: 
						wprintf (L"IBM\n"); 
						break; 
					case 4: 
						wprintf (L"Toshiba\n"); 
						break; 
					case 5: 
						wprintf (L"3COM\n"); 
						break; 
					case 6: 
						wprintf (L"Microsoft\n"); 
						break; 
					case 7: 
						wprintf (L"Lucent\n"); 
						break; 
					case 8: 
						wprintf (L"Motorola\n"); 
						break; 
					case 9: 
						wprintf (L"Infineon\n"); 
						break; 
					case 10: 
						wprintf (L"CSR\n"); 
						break; 
					case 11: 
						wprintf (L"Silicon Wave\n"); 
						break; 
					case 12: 
						wprintf (L"Digianswer\n"); 
						break; 
					default: 
						wprintf (L"Unknown, code %d\n", bv.manufacturer); 
						break; 
					} 
	


				}

	int iDatum; 
				
					ilen = sizeof(iDatum); 
 
				iRes = getsockopt (s, SOL_RFCOMM, SO_BTH_GET_PAGE_TO, (char *)&iDatum, &ilen); 
				if (iRes) 
					wprintf (L"SO_BTH_GET_PAGE_TO : error %d\n", iRes); 
				else 
					wprintf (L"SO_BTH_GET_PAGE_TO returns 0x%08x (%d)\n", iDatum, iDatum); 

	if ((argc == 2) && (wcsicmp (argv[1], L"manage") == 0)) { 
		SOCKET s = socket (AF_BT, SOCK_STREAM, BTHPROTO_RFCOMM); 
		for ( ; ; ) { 
			wprintf (L"Management mode. Type 'exit' to exit, 'help' for command list\n> "); 
 
			WCHAR szCommand[BUF_MAX]; 
			if (! fgetws (szCommand, BUF_MAX, stdin)) 
				break; 
 
			WCHAR *szEOL = wcschr (szCommand, L'\n'); 
			if (szEOL) 
				*szEOL = '\0'; 
 
			if (wcsicmp (szCommand, L"EXIT") == 0) 
				break; 
 
			if (wcsicmp (szCommand, L"HELP") == 0) { 
				wprintf (L"EXIT - exit the monitor\n"); 
				wprintf (L"GETVERSIONS - get local version\n"); 
				wprintf (L"GETPAGE, GETCOD, GETSCAN, GETAUTH - retrieve card parameters\n"); 
				wprintf (L"SETCOD 0xhhhhhh, SETPAGE 0xhhhh, SETSCAN 0xhh, SETAUTH 0xhh - set card parameters\n"); 
				wprintf (L"GETNAME hhhhhhhhhhhh - get remote name\n"); 
				continue; 
			} 
 
			if (wcsicmp (szCommand, L"GETVERSION") == 0) { 
				BTH_LOCAL_VERSION bv; 
 
				int iRes; 
				int ilen = sizeof(bv); 
 
				iRes = getsockopt (s, SOL_RFCOMM, SO_BTH_GET_LOCAL_VER, (char *)&bv, &ilen); 
				if (iRes) 
					wprintf (L"SO_BTH_GET_LOCAL_VER : error %d\n", iRes); 
				else { 
					wprintf (L"hci version %d\n", bv.hci_version); 
					wprintf (L"hci revision %d\n", bv.hci_revision); 
					wprintf (L"lmp version %d\n", bv.lmp_version); 
					wprintf (L"lmp revision %d\n", bv.lmp_subversion); 
					wprintf (L"manufacturer: "); 
					switch (bv.manufacturer) { 
					case 0: 
						wprintf (L"Ericsson\n"); 
						break; 
					case 1: 
						wprintf (L"Nokia\n"); 
						break; 
					case 2: 
						wprintf (L"Intel\n"); 
						break; 
					case 3: 
						wprintf (L"IBM\n"); 
						break; 
					case 4: 
						wprintf (L"Toshiba\n"); 
						break; 
					case 5: 
						wprintf (L"3COM\n"); 
						break; 
					case 6: 
						wprintf (L"Microsoft\n"); 
						break; 
					case 7: 
						wprintf (L"Lucent\n"); 
						break; 
					case 8: 
						wprintf (L"Motorola\n"); 
						break; 
					case 9: 
						wprintf (L"Infineon\n"); 
						break; 
					case 10: 
						wprintf (L"CSR\n"); 
						break; 
					case 11: 
						wprintf (L"Silicon Wave\n"); 
						break; 
					case 12: 
						wprintf (L"Digianswer\n"); 
						break; 
					default: 
						wprintf (L"Unknown, code %d\n", bv.manufacturer); 
						break; 
					} 
					DumpFeatures (bv.lmp_features); 
 
				} 
 
				continue; 
			} 
 
			if (wcsicmp (szCommand, L"GETPAGE") == 0) { 
				int iDatum; 
				int iRes; 
				int ilen = sizeof(iDatum); 
 
				iRes = getsockopt (s, SOL_RFCOMM, SO_BTH_GET_PAGE_TO, (char *)&iDatum, &ilen); 
				if (iRes) 
					wprintf (L"SO_BTH_GET_PAGE_TO : error %d\n", iRes); 
				else 
					wprintf (L"SO_BTH_GET_PAGE_TO returns 0x%08x (%d)\n", iDatum, iDatum); 
 
				continue; 
			} 
 
			if (wcsicmp (szCommand, L"GETCOD") == 0) { 
				int iDatum; 
				int iRes; 
				int ilen = sizeof(iDatum); 
 
				iRes = getsockopt (s, SOL_RFCOMM, SO_BTH_GET_COD, (char *)&iDatum, &ilen); 
				if (iRes) 
					wprintf (L"SO_BTH_GET_COD : error %d\n", iRes); 
				else 
					wprintf (L"SO_BTH_GET_COD returns 0x%08x (%d)\n", iDatum, iDatum); 
 
				continue; 
			} 
 
			if (wcsicmp (szCommand, L"GETSCAN") == 0) { 
				int iDatum; 
				int iRes; 
				int ilen = sizeof(iDatum); 
 
				iRes = getsockopt (s, SOL_RFCOMM, SO_BTH_GET_SCAN, (char *)&iDatum, &ilen); 
				if (iRes) 
					wprintf (L"SO_BTH_GET_SCAN : error %d\n", iRes); 
				else 
					wprintf (L"SO_BTH_GET_SCAN returns 0x%08x (%d)\n", iDatum, iDatum); 
 
				continue; 
			} 
 
			if (wcsicmp (szCommand, L"GETAUTH") == 0) { 
				int iDatum; 
				int iRes; 
				int ilen = sizeof(iDatum); 
 
				iRes = getsockopt (s, SOL_RFCOMM, SO_BTH_GET_AUTHN_ENABLE, (char *)&iDatum, &ilen); 
				if (iRes) 
					wprintf (L"SO_BTH_GET_AUTHN_ENABLE : error %d\n", iRes); 
				else 
					wprintf (L"SO_BTH_GET_AUTHN_ENABLE returns 0x%08x (%d)\n", iDatum, iDatum); 
 
				continue; 
			} 
 
			if (wcsnicmp (szCommand, L"SETSCAN ", 8) == 0) { 
				int iDatum = 0; 
				int iRes; 
				int ilen = sizeof(iDatum); 
 
				WCHAR *p = szCommand + 8; 
 
				if (! GetUx (&p, &iDatum, 2)) { 
					wprintf (L"Syntax: expected hex number, 0xhh\n"); 
					continue; 
				} 
 
				iRes = setsockopt (s, SOL_RFCOMM, SO_BTH_SET_SCAN, (char *)&iDatum, ilen); 
				if (iRes) 
					wprintf (L"SO_BTH_SET_SCAN : error %d\n", iRes); 
 
				continue; 
			} 
 
			if (wcsnicmp (szCommand, L"SETAUTH ", 8) == 0) { 
				int iDatum = 0; 
				int iRes; 
				int ilen = sizeof(iDatum); 
 
				WCHAR *p = szCommand + 8; 
 
				if (! GetUx (&p, &iDatum, 2)) { 
					wprintf (L"Syntax: expected hex number, 0xhh\n"); 
					continue; 
				} 
 
				iRes = setsockopt (s, SOL_RFCOMM, SO_BTH_SET_AUTHN_ENABLE, (char *)&iDatum, ilen); 
				if (iRes) 
					wprintf (L"SO_BTH_SET_AUTHN_ENABLE : error %d\n", iRes); 
 
				continue; 
			} 
 
			if (wcsnicmp (szCommand, L"SETPAGE ", 8) == 0) { 
				int iDatum = 0; 
				int iRes; 
				int ilen = sizeof(iDatum); 
 
				WCHAR *p = szCommand + 8; 
 
				if (! GetUx (&p, &iDatum, 4)) { 
					wprintf (L"Syntax: expected hex number, 0xhhhh\n"); 
					continue; 
				} 
 
				iRes = setsockopt (s, SOL_RFCOMM, SO_BTH_SET_PAGE_TO, (char *)&iDatum, ilen); 
				if (iRes) 
					wprintf (L"SO_BTH_SET_PAGE_TO : error %d\n", iRes); 
 
				continue; 
			} 
 
			if (wcsnicmp (szCommand, L"SETCOD ", 7) == 0) { 
				int iDatum = 0; 
				int iRes; 
				int ilen = sizeof(iDatum); 
 
				WCHAR *p = szCommand + 7; 
 
				if (! GetUx (&p, &iDatum, 8)) { 
					wprintf (L"Syntax: expected hex number, 0xhhhhhh\n"); 
					continue; 
				} 
 
				iRes = setsockopt (s, SOL_RFCOMM, SO_BTH_SET_COD, (char *)&iDatum, ilen); 
				if (iRes) 
					wprintf (L"SO_BTH_SET_COD : error %d\n", iRes); 
 
				continue; 
			} 
 
			if (wcsnicmp (szCommand, L"GETNAME ", 8) == 0) { 
 
				WCHAR *p = szCommand + 8; 
 
				BTH_REMOTE_NAME r; 
 
				if (! GetBA (&p, &r.bt)) { 
					wprintf (L"Syntax: expected bluetooth address\n"); 
					continue; 
				} 
 
				int ilen = sizeof(r); 
				int iRes = setsockopt (s, SOL_RFCOMM, SO_BTH_SET_READ_REMOTE_NAME, (char *)&r, ilen); 
 
				if (iRes) 
					wprintf (L"SO_BTH_SET_READ_REMOTE_NAME : error %d\n", iRes); 
				else 
					wprintf (L"Name: %s\n", r.szNameBuffer); 
 
				continue; 
			} 
 
		} 
 
		closesocket (s); 
		return 0; 
	} 
 
	if ((argc >= 4) && (wcsicmp (argv[1], L"client") == 0) && GetBA(&arg2, &b)) { 
		SOCKET s = socket (AF_BT, SOCK_STREAM,BTHPROTO_RFCOMM); 
		if (s == INVALID_SOCKET) { 
			wprintf (L"socket failed, error %d\n", WSAGetLastError ()); 
			return 0; 
		} 
 
		if (! ProcessSockOpts (s, argv + 4, argc - 4)) { 
			closesocket(s); 
			return 0; 
		} 
 
		SOCKADDR_BTH sa; 
		memset (&sa, 0, sizeof(sa)); 
 
		sa.addressFamily = AF_BT; 
 
		sa.btAddr = b; 
 
		if (! GetDI(&arg3, &channel)) { 
			wprintf(L"Invalid format for Channel specified\n"); 
			closesocket(s); 
 
			return 0; 
		} 
 
		sa.port = channel & 0xff; 
 
		wprintf (L"Connecting to %04x%08x 0x%02x\n", GET_NAP(b), GET_SAP(b), channel & 0xff); 
 
		if (connect (s, (SOCKADDR *)&sa, sizeof(sa))) { 
			wprintf (L"Connect failed, error = %d\n", WSAGetLastError ()); 
			return 0; 
		} 
 
		SOCKADDR_BTH sa3; 
		int namelen = sizeof(sa3); 
		if (0 == getsockname(s, (SOCKADDR *)&sa3, &namelen))	{ 
			wprintf (L"Socket s:localname<%04x%08x> connecting on port %d(0x%x)...\n", GET_NAP(sa3.btAddr), GET_SAP(sa3.btAddr), sa3.port, sa3.port); 
		} 
 
		namelen = sizeof(sa3); 
		if (0 == getpeername(s, (SOCKADDR *)&sa3, &namelen))	{ 
			wprintf (L"Socket s:peername<%04x%08x> connecting on port %d(0x%x)...\n", GET_NAP(sa3.btAddr), GET_SAP(sa3.btAddr), sa3.port, sa3.port); 
		} 
 
		wprintf (L"Established connection with %04x%08x 0x%02x\n", GET_NAP(b), GET_SAP(b), channel & 0xff); 
		CloseHandle (CreateThread(NULL, 0, ReadThread, (LPVOID)s, 0, NULL)); 
		WriteThread ((LPVOID)s); 
	} else if ((argc >= 3) && (wcsicmp (argv[1], L"server") == 0)) { 
		SOCKET s = socket (AF_BT, SOCK_STREAM, BTHPROTO_RFCOMM); 
		if (s == INVALID_SOCKET) { 
			wprintf (L"socket failed, error %d\n", WSAGetLastError ()); 
			return 0; 
		} 
 
		SOCKADDR_BTH sa; 
		memset (&sa, 0, sizeof(sa)); 
 
		sa.addressFamily = AF_BT; 
 
		if (! GetDI (&arg2, &channel)) { 
			wprintf(L"Invalid format for Channel specified\n"); 
			closesocket(s); 
 
			return 0; 
		} 
 
		sa.port = channel & 0xff; 
 
		wprintf (L"binding to 0x%02x\n", channel & 0xff); 
 
		if (bind (s, (SOCKADDR *)&sa, sizeof(sa))) { 
			wprintf (L"Bind failed, error = %d\n", WSAGetLastError ()); 
			closesocket(s); 
			return 0; 
		} 
 
		int namelen = sizeof(sa); 
		if (getsockname(s, (SOCKADDR *)&sa, &namelen))	{ 
			wprintf(L"getsockname failed, error = %d\n", WSAGetLastError()); 
			closesocket(s); 
			return 0; 
		} 
			 
		if (! ProcessSockOpts (s, argv + 3, argc - 3)) { 
			closesocket(s); 
			return 0; 
		} 
 
		wprintf (L"localhost<%04x%08x> listening on port %d(0x%x)...\n", GET_NAP(sa.btAddr), GET_SAP(sa.btAddr), sa.port, sa.port); 
 
		if (listen (s, 5)) { 
			wprintf (L"Listen failed, error = %d\n", WSAGetLastError ()); 
			return 0; 
		} 
 
 
		for ( ; ; ) { 
			SOCKADDR_BTH sa2; 
			int size = sizeof(sa2); 
 
			wprintf (L"Accepting...\n"); 
 
			SOCKET s2 = accept (s, (SOCKADDR *)&sa2, &size); 
 
			if (s2 == INVALID_SOCKET) { 
				wprintf (L"Accept failed, error = %d\n", WSAGetLastError ()); 
				break; 
			} 
 
			if (size != sizeof(sa2)) 
				wprintf (L"Sockaddr size is %d, not %d which was expected!\n", size, sizeof(sa2)); 
 
			BT_ADDR b2 = sa2.btAddr; 
			int channel2 = sa2.port; 
 
			SOCKADDR_BTH sa3; 
			namelen = sizeof(sa3); 
			if (0 == getsockname(s2, (SOCKADDR *)&sa3, &namelen))	{ 
				wprintf (L"Socket s2:localname<%04x%08x> connecting on port %d(0x%x)...\n", GET_NAP(sa3.btAddr), GET_SAP(sa3.btAddr), sa3.port, sa3.port); 
			} 
 
			namelen = sizeof(sa3); 
			if (0 == getpeername(s2, (SOCKADDR *)&sa3, &namelen))	{ 
				wprintf (L"Socket s2:peername<%04x%08x> connecting on port %d(0x%x)...\n", GET_NAP(sa3.btAddr), GET_SAP(sa3.btAddr), sa3.port, sa3.port); 
			} 
		 
 
			wprintf (L"Connection accepted. Family %d Address %04x%08x Channel 0x%02x\n", sa2.addressFamily, GET_NAP(b2), GET_SAP(b2), channel2); 
			CloseHandle (CreateThread(NULL, 0, ReadThread, (LPVOID)s2, 0, NULL)); 
			CloseHandle (CreateThread(NULL, 0, WriteThread, (LPVOID)s2, 0, NULL)); 
		} 
	} else { 
		wprintf (L"Usage: %s {server | client } channel {AUTH} {ENCRYPT}\n", argv[0]); 
		wprintf (L"\t\t{MTU dec. number} {MTUMIN dec. number} {MTUMAX dec. number}\n"); 
		wprintf (L"\t\t{XON dec. number} {XOFF dec. number}\n"); 
		wprintf (L"\t\t{SENDBUFF dec. number} {RECVBUFF dec. number}\n"); 
		wprintf (L"Or: %s manage\n", argv[0]); 
		return 1; 
	} 
 
	return 0; 
} 








