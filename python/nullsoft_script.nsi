# Define the computer name and the service name
$remoteComputer = "USCEDMXL9414N6G"
$serviceName = "ATI Logging ETAS Usage Service"

# Create a WMI object to connect to the remote computer
$wmi = Get-WmiObject -Class Win32_Service -ComputerName $remoteComputer -Filter "Name='$serviceName'"

# Stop the service
$wmi.StopService()
