function Stop-ServiceByName {
	param (
		[Parameter(Mandatory=$true)][string] $serviceName,
		[Parameter(Mandatory=$false)][string] $computerName = $env:COMPUTERNAME  # If computerName is not specified, it will pick the local machine
	)
	try {
		Stop-Service -Name $serviceName -ComputerName $computerName -ErrorAction Stop
	} catch {
		Write-Host "Failed to stop $serviceName service, error: $_" -ForegroundColor Red
		Read-Host -Prompt "Press Enter to exit"
		exit
	}
}

Stop-ServiceByName -serviceName "ATI Logging ETAS Usage Service"
