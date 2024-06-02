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

# Path to the new executable
$newExecutablePath = "C:\Project\Debug\NewExecutable.exe"

# Convert the new executable to base64
$newExecutableBase64 = [Convert]::ToBase64String([IO.File]::ReadAllBytes($newExecutablePath))

# Prompt for the new Log on As account username and password
$username = Read-Host "Enter the username for the Log on As account"
$password = Read-Host -AsSecureString "Enter the password for the Log on As account"

# Loop through the selected computers and stop the service on each
foreach ($computer in $selectedComputers) {
    # Create a WMI object to connect to the selected computer
    $wmi = Get-WmiObject -Class Win32_Service -ComputerName $computer -Filter "Name='$serviceName'"

    # Stop the service
    $wmi.StopService()

    Write-Host "Stopped service on $computer"

    # Convert the base64-encoded string to bytes and save as the new executable
    $newExecutableBytes = [System.Convert]::FromBase64String($newExecutableBase64)
    [System.IO.File]::WriteAllBytes("\\$computer\C$\Service\NewExecutable.exe", $newExecutableBytes)
    Write-Host "Copied new executable to $computer"

    # Change the Log on As account for the service
    $service = Get-WmiObject -Class Win32_Service -ComputerName $computer -Filter "Name='$serviceName'"
    $service.Change($null, $null, $null, $null, $null, $null, "$username", $password, $null, $null, $null)
    Write-Host "Changed Log on As account for service on $computer"
}

# Stop the service on the local computer
$wmiLocal = Get-WmiObject -Class Win32_Service -Filter "Name='$serviceName'"
$wmiLocal.StopService()
Write-Host "Stopped service on $($env:COMPUTERNAME)"

# Convert the base64-encoded string to bytes and save as the new executable on the local computer
$newExecutableBytesLocal = [System.Convert]::FromBase64String($newExecutableBase64)
[System.IO.File]::WriteAllBytes("C:\Service\NewExecutable.exe", $newExecutableBytesLocal)
Write-Host "Copied new executable to $($env:COMPUTERNAME)"

# Change the Log on As account for the service on the local computer
$serviceLocal = Get-WmiObject -Class Win32_Service -Filter "Name='$serviceName'"
$serviceLocal.Change($null, $null, $null, $null, $null, $null, "$username", $password, $null, $null, $null)
Write-Host "Changed Log on As account for service on $($env:COMPUTERNAME)"
