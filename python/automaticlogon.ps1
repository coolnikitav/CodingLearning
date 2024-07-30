function Stop-ServiceByName {
    param (
        [Parameter(Mandatory=$true)][string] $serviceName,
        [Parameter(Mandatory=$false)][string] $computerName = $env:COMPUTERNAME  # If computerName is not specified, it will pick the local machine
    )

    try {
        if ($computerName -eq $env:COMPUTERNAME) {
            Stop-Service -Name $serviceName -ErrorAction Stop
        } else {
            Invoke-Command -ComputerName $computerName -ScriptBlock {
                param ($serviceName)
                Stop-Service -Name $serviceName -ErrorAction Stop
            } -ArgumentList $serviceName
        }
        Write-Host "Service '$serviceName' stopped successfully on '$computerName'."
    } catch {
        Write-Host "Failed to stop $serviceName service on $computerName, error: $_" -ForegroundColor Red
        Read-Host -Prompt "Press Enter to exit"
        exit
    }
}

# Example usage:
Stop-ServiceByName -serviceName "ATI Logging ETAS Usage Service"
# To stop service on a remote computer, specify the computer name
# Stop-ServiceByName -serviceName "ATI Logging ETAS Usage Service" -computerName "RemoteComputerName"

I tried stopping the service on another computer and getting the following error:


Failed to stop ATI Logging ETAS Usage Service service on USCED2UA81121M2, error: [USCED2UA81121M2] Connecting to remote server USCED2UA81121M2 failed with the following error message : The client cannot connect to the destination specified in the request. Verify that the service on the destination is running and is accepting requests. Consult the logs and documentation for the WS-Management service running on the destination, most commonly IIS or WinRM. If the destination is the WinRM service, run the following command on the destination to analyze and configure the WinRM service: "winrm quickconfig". For more information, see the about_Remote_Troubleshooting Help topic.

FYI, the computer is on the network. I can access its files by typing in \\USCED2UA81121M2\c$ in file explorer.

Test-WSman : <f:WSManFault xmlns:f="http://schemas.microsoft.com/wbem/wsman/1/wsmanfault" Code="2150858770"
Machine="USCED2UA81121L8.CORP.ALSN.COM"><f:Message>The client cannot connect to the destination specified in the
request. Verify that the service on the destination is running and is accepting requests. Consult the logs and
documentation for the WS-Management service running on the destination, most commonly IIS or WinRM. If the destination
is the WinRM service, run the following command on the destination to analyze and configure the WinRM service: "winrm
quickconfig". </f:Message></f:WSManFault>
At line:1 char:1
+ Test-WSman -ComputerName USCED2UA81121M2
+ ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    + CategoryInfo          : InvalidOperation: (USCED2UA81121M2:String) [Test-WSMan], InvalidOperationException
    + FullyQualifiedErrorId : WsManError,Microsoft.WSMan.Management.TestWSManCommand

$computers = @("Computer1", "Computer2", "Computer3")
$serviceName = "ATI Logging ETAS Usage Service"

foreach ($computer in $computers) {
    try {
        $service = Get-WmiObject -Class Win32_Service -ComputerName $computer -Filter "Name='$serviceName'"
        $service.StopService()
        Write-Host "Stopped service '$serviceName' on $computer."
    }
    catch {
        Write-Host "Failed to stop service '$serviceName' on $computer. Error: $_" -ForegroundColor Red
    }
}
