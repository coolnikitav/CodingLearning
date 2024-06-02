OutFile "RemoteInstaller.exe"
Name "Remote Service Stopper"
InstallDir "$INSTDIR"

RequestExecutionLevel admin

Var REMOTE_COMPUTER

Section "Stop Service on Remote Computers"

  ; Define the remote computers
  StrCpy $REMOTE_COMPUTER "Computer1"
  Call StopServiceOnRemote
  StrCpy $REMOTE_COMPUTER "Computer2"
  Call StopServiceOnRemote
  ; Add more computers as needed

SectionEnd

Function StopServiceOnRemote

  ; Define the command to stop the service on the remote machine
  StrCpy $0 "psexec \\\\$REMOTE_COMPUTER -u admin_user -p admin_password net stop \"ATI Logging ETAS Usage Service\""

  ; Run the stop service command using PsExec
  DetailPrint "Executing: $0"
  nsExec::ExecToStack $0

  ; Check execution result and log output
  Pop $1
  StrCmp $1 0 Success
  DetailPrint "Command failed with error code $1"
  ; Log the output from the stack
  ${Do}
    Pop $2
    StrCmp $2 "" DoneOutput
    DetailPrint $2
  ${Loop}
DoneOutput:

  MessageBox MB_OK|MB_ICONERROR "Failed to stop service on $REMOTE_COMPUTER"
  Quit

Success:
  MessageBox MB_OK|MB_ICONINFORMATION "Service stopped successfully on $REMOTE_COMPUTER"

FunctionEnd

