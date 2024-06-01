OutFile "RemoteInstaller.exe"
Name "SimInstallerScript_Only_WindowsUsageService"
InstallDir "$INSTDIR"

RequestExecutionLevel admin

Var REMOTE_COMPUTER

Section "Install"

  ; Define the remote computers
  StrCpy $REMOTE_COMPUTER "Computer1"
  Call InstallServiceOnRemote
  StrCpy $REMOTE_COMPUTER "Computer2"
  Call InstallServiceOnRemote
  ; Add more computers as needed

SectionEnd

Function InstallServiceOnRemote

  ; Define the remote script commands
  !define REMOTE_SCRIPT "
    net stop \"ATI Logging ETAS Usage Service\" && \
    sc.exe config \"ATI Logging ETAS Usage Service\" start= auto obj= \"svc_SIMadministrator\" password= \"password\" && \
    net localgroup Administrators svc_SIMadministrator@CORP.ALSN.com /add && \
    reg add HKLM\\SOFTWARE\\Allison Transmission\\G5HTL\\ExceptionDetails /v TimeoutTime /t REG_SZ /d \"\" /f && \
    net start \"ATI Logging ETAS Usage Service\""

  ; Embed the new executable within the installer
  File "C:\ETAS_SIM5\Working\Debug\new_service.exe"

  ; Copy the embedded executable to the remote machine
  nsExec::ExecToLog 'psexec \\$REMOTE_COMPUTER -u admin_user -p admin_password cmd.exe /c copy /Y "%~dp0new_service.exe" "C:\ETASData\SupportApps\new_service.exe"'

  ; Run the remote script using PsExec
  nsExec::ExecToLog 'psexec \\$REMOTE_COMPUTER -u admin_user -p admin_password cmd.exe /c ${REMOTE_SCRIPT}'

  ; Check execution result
  Pop $0
  StrCmp $0 0 Done

  MessageBox MB_OK|MB_ICONERROR "Failed to install service on $REMOTE_COMPUTER"
  Quit

Done:
  MessageBox MB_OK|MB_ICONINFORMATION "Service installed successfully on $REMOTE_COMPUTER"

FunctionEnd
