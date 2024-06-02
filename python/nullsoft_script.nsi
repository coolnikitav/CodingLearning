# Define the computer name and the service name
$remoteComputer = "ComputerB"
$serviceName = "NameOfService"

# Create a WMI object to connect to the remote computer
$wmi = Get-WmiObject -Class Win32_Service -ComputerName $remoteComputer -Filter "Name='$serviceName'"

# Stop the service
$wmi.StopService()
