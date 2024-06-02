# Define the list of computers
$computers = @(
    "Computer1",
    "Computer2",
    "Computer3",
    # Add more computers as needed
)

# Display a menu for selecting a computer
Write-Host "Select a computer:"
for ($i = 0; $i -lt $computers.Count; $i++) {
    Write-Host "$($i + 1). $($computers[$i])"
}

# Get user input for selecting a computer
$selection = Read-Host "Enter the number of the computer"

# Validate the user input
if ($selection -ge 1 -and $selection -le $computers.Count) {
    $selectedComputer = $computers[$selection - 1]

    # Define the service name
    $serviceName = "NameOfService"

    # Create a WMI object to connect to the selected computer
    $wmi = Get-WmiObject -Class Win32_Service -ComputerName $selectedComputer -Filter "Name='$serviceName'"

    # Stop the service
    $wmi.StopService()
} else {
    Write-Host "Invalid selection. Please enter a number between 1 and $($computers.Count)."
}
