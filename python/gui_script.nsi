Add-Type -AssemblyName PresentationFramework

# Define the list of computers
$computers = @(
    "USCED2UA81121KW",
	"USCED2UA81121L0",
	"USCED2UA81121L1",
	"USCED2UA81121L2",
	"USCED2UA81121L9",
	"USCED2UA81121LB",
	"USCED2UA81121LD",
	"USCED2UA81121LG",
	"USCED2UA81121LH",
	"USCED2UA81121LJ",
	"USCED2UA81121LK",
	"USCED2UA81121LL",
	"USCED2UA81121LM",
	"USCED2UA81121LP",
	"USCED2UA81121LQ",
	"USCED2UA81121LS",
	"USCED2UA81121LT",
	"USCED2UA81121LW",
	"USCED2UA81121M1",
	"USCED2UA81121M2",
	"USCEDMXL9414N6G",
	"USCEDMXL9414N6H",
	"USCEDMXL9414N6J",
	"USCEDMXL9414N6K",
	"USCEDMXL9414N6L",
	"USCEDMXL9414N6P",
	"USCEDMXL9414N6R",
	"USCEDMXL9414N6S"
)

# Create the XAML for the GUI
[xml]$xaml = @"
<Window xmlns="http://schemas.microsoft.com/winfx/2006/xaml/presentation"
        Title="Select Computers" Height="725" Width="400">
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

# Debugging: Check if the WPF elements are correctly instantiated
if ($null -eq $okButton) { Write-Host "OKButton is null" }
if ($null -eq $cancelButton) { Write-Host "CancelButton is null" }
if ($null -eq $computerListBox) { Write-Host "ComputerListBox is null" }

# Selected computers array
$selectedComputers = @()

# Function to close the window and return the selected computers
$okButton.Add_Click({
	Write-Host "Total items in the ListBox: $($computerListBox.Items.Count)"
	Write-Host "Selected items in the ListBox: $($computerListBox.SelectedItems.Count)"
    foreach ($item in $computerListBox.Items) {
		if ($item.IsSelected) {
			Write-Host "hostname: $($item.Content)"
			$selectedComputers += $item.Content
			Write-Host "Selected computers: $($selectedComputers -join ', ')"
		}		
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

# Debugging: Check if any computers were selected
Write-Host "Selected computers: $($selectedComputers -join ', ')"
Write-Host "Dialog result: $result"

if ($result -ne $true -or $selectedComputers.Count -eq 0) {
    Write-Host "No computers selected. Exiting..."
    exit
}

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
$serviceName = "ATI Logging ETAS Usage Service"

# Path to the new executable
$newExecutablePath = "C:\eng_apps\data\SimTools-UZVLYO\SimTools\Development\C#\VisualStudio\ATILoggingETASUsageService.NET4.8\ATILoggingETASUsageWindowsService\ATILoggingETASUsageWindowsService\bin\Debug\ATILoggingETASUsageWindowsService.exe"

# Convert the new executable to base64
$newExecutableBase64 = [Convert]::ToBase64String([IO.File]::ReadAllBytes($newExecutablePath))

# Prompt for the new Log on As account username and password
$username = Read-Host "Enter the username for the Log on As account"
$password = Read-Host "Enter the password for the Log on As account"

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
$registryPath = "HKLM:\SOFTWARE\Allison Transmission\G5HIL\ExceptionDetails"
$valueName = "TimeoutTime"

# Loop through the selected computers and stop the service on each
foreach ($computer in $selectedComputers) {
    # Create a WMI object to connect to the selected computer
    $wmi = Get-WmiObject -Class Win32_Service -ComputerName $computer -Filter "Name='$serviceName'"

    # Stop the service
    $wmi.StopService()

    Write-Host "Stopped service on $computer"

    # Convert the base64-encoded string to bytes and save as the new executable
    $newExecutableBytes = [System.Convert]::FromBase64String($newExecutableBase64)
    [System.IO.File]::WriteAllBytes("\\$computer\C$\ETASData\SupportApps\ATILoggingETASUsageWindowsService.exe", $newExecutableBytes)
    Write-Host "Copied new executable to $computer"
	
	# Change the Log on As account for the service
    $service = Get-WmiObject -Class Win32_Service -ComputerName $computer -Filter "Name='$serviceName'"
    $service.Change($null, $null, $null, $null, $null, "Automatic", "$username", $password, $null, $null, $null)
    Write-Host "Changed Log on As account and set startup type to Automatic for service on $computer"
	
	# Add the user to the Administrators group
	Add-UserToAdministratorsGroup -computerName $computer -username $username
	
	# Clear the registry value
    Clear-RegistryValue -computerName $computer -registryPath $registryPath -valueName $valueName
	
	# Start the service
	$wmiLocal.StartService()
	Write-Host "Started service on $computer"
}

# Stop the service on the local computer
$wmiLocal = Get-WmiObject -Class Win32_Service -Filter "Name='$serviceName'"
$wmiLocal.StopService()
Write-Host "Stopped service on $($env:COMPUTERNAME)"

# Convert the base64-encoded string to bytes and save as the new executable on the local computer
$newExecutableBytesLocal = [System.Convert]::FromBase64String($newExecutableBase64)
[System.IO.File]::WriteAllBytes("C:\ETASData\SupportApps\ATILoggingETASUsageWindowsService.exe", $newExecutableBytesLocal)
Write-Host "Copied new executable to $($env:COMPUTERNAME)"

# Change the Log on As account for the service on the local computer
$serviceLocal = Get-WmiObject -Class Win32_Service -Filter "Name='$serviceName'"
$serviceLocal.Change($null, $null, $null, $null, $null, $null, "$username", $password, $null, $null, $null)
Write-Host "Changed Log on As account and set startup type to Automatic for service on $($env:COMPUTERNAME)"

# Add the user to the Administrators group on the local computer
Add-UserToAdministratorsGroup -computerName $env:COMPUTERNAME -username $username

# Clear the registry value on the local computer
Clear-RegistryValue -computerName $env:COMPUTERNAME -registryPath $registryPath -valueName $valueName

# Start the service
$wmiLocal.StartService()
Write-Host "Started service on $($env:COMPUTERNAME)"

Total items in the ListBox: 28
Selected items in the ListBox: 2
hostname: USCEDMXL9414N6G
Selected computers: USCEDMXL9414N6G
hostname: USCEDMXL9414N6J
Selected computers: USCEDMXL9414N6GUSCEDMXL9414N6J
Selected computers:
Dialog result: True
No computers selected. Exiting...
