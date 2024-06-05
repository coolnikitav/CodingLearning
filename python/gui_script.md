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

# Create a new window
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

$reader = (New-Object System.Xml.XmlNodeReader $xaml)
$window = [Windows.Markup.XamlReader]::Load($reader)

# Function to close the window and return the selected computers
$selectedComputers = @()
$window.OKButton.Add_Click({
    $window.ComputerListBox.SelectedItems | ForEach-Object {
        $selectedComputers += $_.Content
    }
    $window.Close()
})

# Function to close the window without selecting computers
$window.CancelButton.Add_Click({
    $window.Close()
})

$window.ShowDialog() | Out-Null

if ($selectedComputers.Count -eq 0) {
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
$re
