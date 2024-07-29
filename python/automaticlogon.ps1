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
