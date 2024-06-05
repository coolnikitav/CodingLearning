Add-Type -AssemblyName PresentationFramework

# Define the list of computers
$computers = @(
    "Computer1",
    "Computer2",
    "Computer3",
    # Add more computers as needed
)

# Add the local computer to the list
$computers += $env:COMPUTERNAME

# Create the XAML for the GUI
[xml]$xaml = @"
<Window xmlns="http://schemas.microsoft.com/winfx/2006/xaml/presentation"
        Title="Select Computers" Height="300" Width="400">
    <Grid>
        <Grid.RowDefinitions>
            <RowDefinition Height="Auto" />
            <RowDefinition Height="*" />
            <RowDefinition Height="Auto" />
        </Grid.RowDefinitions>
        <TextBlock Text="Select computers to stop the service on:" Margin="10" />
        <ListBox Name="ComputerListBox" Grid.Row="1" Margin="10" SelectionMode="Multiple">
            $($computers | ForEach-Object { "<ListBoxItem Content='$_' />" })
        </ListBox>
        <StackPanel Grid.Row="2" Orientation="Horizontal" HorizontalAlignment="Center" Margin="10">
            <Button Name="OKButton" Content="OK" Width="75" Margin="5" />
            <Button Name="CancelButton" Content="Cancel" Width="75" Margin="5" />
        </StackPanel>
    </Grid>
</Window>
"@

# Load the XAML
$reader = (New-Object System.Xml.XmlNodeReader $xaml)
$window = [Windows.Markup.XamlReader]::Load($reader)

# Get the WPF elements
$okButton = $window.FindName("OKButton")
$cancelButton = $window.FindName("CancelButton")
$computerListBox = $window.FindName("ComputerListBox")

# Selected computers array
$selectedComputers = @()

# Function to close the window and return the selected computers
$okButton.Add_Click({
    $computerListBox.SelectedItems | ForEach-Object {
        $selectedComputers += $_.Content
    }
    $window.DialogResult = $true
    $window.Close()
})

# Function to close the window without selecting computers
$cancelButton.Add_Click({
    $window.DialogResult = $false
    $window.Close()
})

# Show the window as a dialog and capture the result
$result = $window.ShowDialog()

# Check if any computers were selected
if ($result -ne $true -or $selectedComputers.Count -eq 0) {
    Write-Host "No computers selected. Exiting..."
    exit
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

# Function to add a user to the Administrators group
function Add-UserToAdministratorsGroup {
    param (
        [string]$computerName,
        [string]$username
    )
    $group = [ADSI]"WinNT://$computerName/Administrators,group"
    $user = [ADSI]"WinNT://$computerName/$username,user"
    $group.Add($user.Path)
    Write-Host "Added $username to Administrators group on $computerName"
}

# Function to clear the registry value
function Clear-RegistryValue {
    param (
        [string]$computerName,
        [string]$registryPath,
        [string]$valueName
    )
    Invoke-Command -ComputerName $computerName -ScriptBlock {
        param ($registryPath, $valueName)
        Remove-ItemProperty -Path $registryPath -Name $valueName -ErrorAction SilentlyContinue
        Write-Host "Cleared registry value $valueName under $registryPath on $env:COMPUTERNAME"
    } -ArgumentList $registryPath, $valueName
}

# Define the registry path and value name
$registryPath = "HKLM:\SOFTWARE\TimeoutTime"
$valueName = "YourRegistryValueName"

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

    # Add the user to the Administrators group
    Add-UserToAdministratorsGroup -computerName $computer -username $username

    # Clear the registry value
    Clear-RegistryValue -computerName $computer -registryPath $registryPath -valueName $valueName

    # Change the Log on As account and set the startup type to automatic for the service
    $service = Get-WmiObject -Class Win32_Service -ComputerName $computer -Filter "Name='$serviceName'"
    $service.Change($null, $null, $null, $null, $null, "Automatic", "$username", $password, $null, $null, $null)
    Write-Host "Changed Log on As account and set startup type to Automatic for service on $computer"

    # Start the service
    $wmi.StartService()
    Write-Host "Started service on $computer"
}

# Stop the service on the local computer
$wmiLocal = Get-WmiObject -Class Win32_Service -Filter "Name='$serviceName'"
$wmiLocal.StopService()
Write-Host "Stopped service on $($env:COMPUTERNAME)"

# Convert the base64-encoded string to bytes and save as the new executable on the local computer
$newExecutableBytesLocal = [System.Convert]::FromBase64String($newExecutableBase64)
[System.IO.File]::WriteAllBytes("C:\Service\NewExecutable.exe", $newExecutableBytesLocal)
Write-Host "Copied new executable to $($env:COMPUTERNAME)"

# Add the user to the Administrators group on the local computer
Add-UserToAdministratorsGroup -computerName $env:COMPUTERNAME -username $username

# Clear the registry value on the local computer
Clear-RegistryValue -computerName $env:COMPUTERNAME -registryPath $registryPath -valueName $valueName

# Change the Log on As account and set the startup type to automatic for the service on the local computer
$serviceLocal = Get-WmiObject -Class Win32_Service -Filter "Name='$serviceName'"
$serviceLocal.Change($null, $null, $null, $null, $null, "Automatic", "$username", $password, $null, $null, $null)
Write-Host "Changed Log on As account and set startup type to Automatic for service on $($env:COMPUTERNAME)"

# Start the service on the local computer
$wmiLocal.StartService()
Write-Host "Started service on $($env:COMPUTERNAME)"
