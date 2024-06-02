Section "Stop Service"
    ; Define variables
    Var /GLOBAL REMOTE_HOST
    Var /GLOBAL SERVICE_NAME
    Var /GLOBAL PSEXEC_PATH

    ; Assign values to variables
    StrCpy $REMOTE_HOST "\\hostname"
    StrCpy $SERVICE_NAME "ServiceName"
    StrCpy $PSEXEC_PATH "C:\Path\To\PsExec.exe"

    ; Execute the PsExec command to stop the service
    nsExec::ExecToLog '"$PSEXEC_PATH" $REMOTE_HOST -u yourUsername -p yourPassword sc stop $SERVICE_NAME'
    Pop $0

    ; Check if the command was successful
    StrCmp $0 "0" done
    MessageBox MB_OK|MB_ICONEXCLAMATION "Failed to stop the service on $REMOTE_HOST"
    Abort

    done:
    MessageBox MB_OK "Service stopped successfully on $REMOTE_HOST"
SectionEnd
