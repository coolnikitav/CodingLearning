# Define the list of computers
$computers = @(
    "Computer1",
    "Computer2",
    "Computer3",
    # Add more computers as needed
)

# Add the local computer to the list
$computers += $env:COMPUTERNAME

# Display a menu for selecting computers
Write-Host "Select computers to stop the service on (separate numbers by commas):"
for ($i = 0; $i -lt $computers.Count; $i++) {
    Write-Host "$($i + 1). $($computers[$i])"
}

# Get user input for selecting computers
$selection = Read-Host "Enter the numbers of the computers (e.g., '1,3' for Computer1 and Computer3)"

# Convert the user input to an array of selected computer numbers
$selectedNumbers = $selection -split "," | ForEach-Object { $_.Trim() }

# Validate the user input
$selectedComputers = @()
foreach ($number in $selectedNumbers) {
    if ($number -ge 1 -and $number -le $computers.Count) {
        $selectedComputers += $computers[$number - 1]
    } else {
        Write-Host "Invalid selection: $number"
    }
}

# Define the service name
$serviceName = "NameOfService"

# Loop through the selected computers and stop the service on each
foreach ($computer in $selectedComputers) {
    # Create a WMI object to connect to the selected computer
    $wmi = Get-WmiObject -Class Win32_Service -ComputerName $computer -Filter "Name='$serviceName'"

    # Stop the service
    $wmi.StopService()

    Write-Host "Stopped service on $computer"
}
