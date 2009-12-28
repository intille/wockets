/*
This program starts ActiveSync with .ini file as a parameter.
.ini file should be located in the same folder. Name of this file 
should be passed as a parameter. If no parameter is given then 
default name is used. Default .ini file name is install.ini

Copyright: Pocket PC Developer Network
License: Free, AS IS
*/

#include "stdafx.h"
#include <string.h>
#include <process.h>
#include <winreg.h> 

#define TITLE "Installation"
#define ACTIVESYNC_REGISTRY_PATH "SOFTWARE\\Microsoft\\Windows\\CurrentVersion\\App Paths\\CEAPPMGR.EXE"
#define ERROR_NOACTIVESYNC "Can not find ActiveSync. Please reinstall ActiveSync and than run this installation again."

int APIENTRY WinMain(HINSTANCE hInstance,
                     HINSTANCE hPrevInstance,
                     LPSTR     lpCmdLine,
                     int       nCmdShow)
{
	char strActuveSyncPath[MAX_PATH];
	HKEY hActiveSyncKey;

	//Read Microsoft ActiveSync registry key
	LONG res = RegOpenKeyEx(HKEY_LOCAL_MACHINE, ACTIVESYNC_REGISTRY_PATH, 0, KEY_READ, &hActiveSyncKey);
	if (ERROR_SUCCESS!=res) {
		::MessageBox(NULL, ERROR_NOACTIVESYNC, TITLE, MB_OK | MB_ICONERROR);
		return 0;
	}

	DWORD dwLength = MAX_PATH;
	DWORD dwType;

	//Read Microsoft ActiveSync path
	res = RegQueryValueEx(hActiveSyncKey, NULL, NULL, &dwType, (unsigned char *)strActuveSyncPath, &dwLength);
	RegCloseKey(hActiveSyncKey);

	if (ERROR_SUCCESS!=res) {
		::MessageBox(NULL, ERROR_NOACTIVESYNC, TITLE, MB_OK | MB_ICONERROR);
		return 0;
	}

	//Start ActiveSync with the given of default .ini file as a parameter
	if ((*lpCmdLine)==0) {
		char currentDirectory[MAX_PATH];
		::GetCurrentDirectory(MAX_PATH, currentDirectory);
		char iniPath[MAX_PATH];
		strcpy(iniPath, "\"");
		strcat(iniPath, currentDirectory);
		strcat(iniPath, "\\install.ini\"");
		_execl(strActuveSyncPath, strActuveSyncPath, iniPath, NULL);
	} else {
		_execl(strActuveSyncPath, strActuveSyncPath, lpCmdLine, NULL);
	}

	return 0;
}



