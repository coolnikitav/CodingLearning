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
        Title="Select Computers" Height="350" Width="400">
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
            <Button Name="SelectAllButton" Content="Select All" Width="75" Margin="5" />
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
$selectAllButton = $window.FindName("SelectAllButton")

# Selected computers array
$selectedComputers = New-Object System.Collections.ObjectModel.ObservableCollection[System.String]
$selectAllState = [ref] $false

# Function to close the window and return the selected computers
$okButton.Add_Click({
    $computerListBox.SelectedItems | ForEach-Object {
        $selectedComputers.Add($_.Content)
    }
    $window.DialogResult = $true
    $window.Close()
})

# Function to close the window without selecting computers
$cancelButton.Add_Click({
    $window.DialogResult = $false
    $window.Close()
})

# Function to toggle select all / deselect all
$selectAllButton.Add_Click({
    if ($selectAllState.Value -eq $false) {
        $computerListBox.SelectAll()
        $selectAllButton.Content = "Deselect All"
    } else {
        $computerListBox.UnselectAll()
        $selectAllButton.Content = "Select All"
    }
    $selectAllState.Value = -not $selectAllState.Value
})

# Show the window as a dialog and capture the result
$result = $window.ShowDialog()

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
    $group.Add($user.Path) | Out-Null
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
        Remove-ItemProperty -Path $registryPath -Name $valueName -ErrorAction SilentlyContinue | Out-Null
        Write-Host "Cleared registry value $valueName under $registryPath on $env:COMPUTERNAME"
    } -ArgumentList $registryPath, $valueName
}

# Define the registry path and value name
$registryPath = "HKLM:\SOFTWARE\TimeoutTime"
$valueName = "YourRegistryValueName"

# Function to stop the service and wait for it to stop completely
function Stop-ServiceAndWait {
    param (
        [string]$computerName,
        [string]$serviceName
    )
    $service = Get-Service -ComputerName $computerName -Name $serviceName
    if ($service.Status -eq 'Running') {
        $service | Stop-Service -Force
        Start-Sleep -Seconds 10
        $service = Get-Service -ComputerName $computerName -Name $serviceName
        while ($service.Status -ne 'Stopped') {
            Start-Sleep -Seconds 5
            $service = Get-Service -ComputerName $computerName -Name $serviceName
        }
        Write-Host "Service $serviceName stopped on $computerName"
    } else {
        Write-Host "Service $serviceName is already stopped on $computerName"
    }
}

# Function to change the Log On As account and set startup type
function Set-ServiceLogOnAsAndStartupType {
    param (
        [string]$computerName,
        [string]$serviceName,
        [string]$username,
        [System.Security.SecureString]$password
    )
    $service = Get-WmiObject -Class Win32_Service -ComputerName $computerName -Filter "Name='$serviceName'"
    $result = $service.Change($null, $null, $null, $null, $null, "Automatic", "$username", $password, $null, $null, $null)
    
    if ($result.ReturnValue -eq 0) {
        Write-Host "Changed Log on As account and set startup type to Automatic for service on $computerName"
    } else {
        Write-Host "Failed to change Log on As account or set startup type on $computerName. ReturnValue: $($result.ReturnValue)"
    }
}

# Function to verify service startup type
function Verify-ServiceStartupType {
    param (
        [string]$computerName,
        [string]$serviceName
    )
    $service = Get-WmiObject -Class Win32_Service -ComputerName $computerName -Filter "Name='$serviceName'"
    if ($service.StartMode -eq "Auto") {
        Write-Host "Verified service $serviceName on $computerName is set to Automatic startup"
    } else {
        Write-Host "Service $serviceName on $computerName is not set to Automatic startup. Current startup type: $($service.StartMode)"
    }
}

# Loop through the selected computers and perform the operations
foreach ($computer in $selectedComputers) {
    # Stop the service and wait for it to stop completely
    Stop-ServiceAndWait -computerName $computer -serviceName $serviceName

    # Convert the base64-encoded string to bytes and save as the new executable
    $newExecutableBytes = [System.Convert]::FromBase64String($newExecutableBase64)
    [System.IO.File]::WriteAllBytes("\\$computer\C$\Service\NewExecutable.exe", $newExecutableBytes) | Out-Null
    Write-Host "Copied new executable to $computer"

    # Add the user to the Administrators group
    Add-UserToAdministratorsGroup -computerName $computer -username $username

    # Clear the registry value
    Clear-RegistryValue -computerName $computer -registryPath $registryPath -valueName $valueName

    # Change the Log on As account and set the startup type to automatic for the service
    Set-ServiceLogOnAsAndStartupType -computerName $computer -serviceName $serviceName -username $username -password $password

    # Verify the startup type of the service
    Verify-ServiceStartupType -computerName $computer -serviceName $serviceName

    # Start the service
    $service = Get-Service -ComputerName $computer -Name $serviceName
    $service | Start-Service | Out-Null
    Write-Host "Started service on $computer"
}

# Stop the service on the local computer and wait for it to stop completely
Stop-ServiceAndWait -computerName $env:COMPUTERNAME -serviceName $serviceName

# Convert the base64-encoded string to bytes and save as the new executable on the local
