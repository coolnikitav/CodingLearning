Add-Type -AssemblyName PresentationFramework

# Define the list of computers
$computers = @(
  "computerA",
	"computerB",
	"computerC",
	"computerD"
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
        <TextBlock Text="Select computers to install the service on:" Margin="10" />
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
	#Write-Host "Selected computers: $($selectedComputers -join ', ')"
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
	Write-Host "enter selectAllState: $selectAllState.Value"
	if ($selectAllState.Value -eq $false) {
		$computerListBox.SelectAll()
		$selectAllButton.Content = "Deselect All"
	} else {
		$computerListBox.UnselectAll()
		$SelectAllButton.Content = "Select all"
	}
	$selectAllState.Value = -not $selectAllState.Value
	Write-Host "exit selectAllState: $selectAllState.Value"
})

# Show the window as a dialog and capture the result
$result = $window.ShowDialog()

# Debugging: Check if any computers were selected
Write-Host "Selected computers: $($selectedComputers -join ', ')"

if ($result -ne $true -or $selectedComputers.Count -eq 0) {
    Write-Host "No computers selected. Exiting..."
    exit
}

function Delete-TCMSelfTestShortcuts {
	param (
		[string] $computerName
	)
	$networkPublicDesktopPath = "\\$computerName\C$\Users\Public\Desktop"
	
	try {
		$shortcutsToDelete = Get-ChildItem -Path $networkPublicDesktopPath -Filter "TCMSelfTest*.lnk"
		
		foreach ($shortcut in $shortcutsToDelete) {
			Remove-Item -Path $shortcut.FullName -Force
		}
		
		if ($shortcutsToDelete.Count -eq 0) {
			Write-Host "Deleted all TCMSelfTest shortcuts on $computerName" -ForegroundColor Green
		} else {
			Write-Host "Did not delete all TCMSelfTest shortcuts on $computerName" -ForegroundColor Red
		}
	} catch {
		Write-Host "Failed to access or delete TCMSelfTest shortuct on $computerName : $_" -ForegroundColor Red
	}
}

function Delete-CurrentSelfTestFolder {
	param (
		[string] $computerName
	)
	$networkSelftestFolderPath = "\\$computerName\C$\ETASData\G5HIL\TCMSelfTest"
	
	try {
		Remove-Item -Path $networkSelftestFolderPath -Recurse -Force
		if (Test-Path -Path $networkSelftestFolderPath) {
			Write-Host "Did not delete TCMSelfTest on $computerName" -ForegroundColor Red
		} else {
			Write-Host "Deleted TCMSelfTest on $computerName" -ForegroundColor Green
		}
	} catch {
		Write-Host "Failed to access or delete TCMSelfTest folder on $computerName : $_" -ForegroundColor Red
	}
}

function Create-NewSelfTestFolder {
	param (
		[string] $computerName
	)
	# This code only creates the empty folders:
	# C:\ETASData\G5HIL\TCMSelfTest and C:\ETASData\G5HIL\TCMSelfTest\Code
	New-Item -ItemType Directory -Path "\\$computerName\C$\ETASData\G5HIL\TCMSelfTest"
	New-Item -ItemType Directory -Path "\\$computerName\C$\ETASData\G5HIL\TCMSelfTest\Code"
	
	if (Test-Path -Path "\\$computerName\C$\ETASData\G5HIL\TCMSelfTest") {
		Write-Host "TCMSelfTest folder created under C\EtasData\G5HIL on $computerName" -ForegroundColor Green
	} else {
		Write-Host "TCMSelfTest folder failed to create under C\EtasData\G5HIL on $computerName" -ForegroundColor Red
	}
	if (Test-Path -Path "\\$computerName\C$\ETASData\G5HIL\TCMSelfTest\Code") {
		Write-Host "Code created under C\EtasData\G5HIL\TCMSelfTest on $computerName" -ForegroundColor Green
	} else {
		Write-Host "Code folder failed to create under C\EtasData\G5HIL\TCMSelfTest on $computerName" -ForegroundColor Red
	}
}

function Copy-SelftestUserGuide {
	param (
		[string] $computerName
	)
	if (Test-Path -Path ".\TCMSelfTestUserGuide.docx") {
		Copy-Item -Path ".\TCMSelfTestUserGuide.docx" -Destination "\\$computerName\C$\ETASData\G5HIL\TCMSelfTest"
		if (Test-Path -Path ".\TCMSelfTestUserGuide.docx") {
			Write-Host "TCMSelfTestUserGuide.docx has been copied to C\ETASData\G5HIL\TCMSelfTest" -ForegroundColor Green
		} else {
			Write-Host "TCMSelfTestUserGuide.docx has failed been to copy to C\ETASData\G5HIL\TCMSelfTest" -ForegroundColor Red
		}
	} else {
		Write-Host "TCMSelfTestUserGuide.docx is not found under TCM_SelfTest folder in working directory" -ForegroundColor Red
	}
}

function Copy-SelftestCode {
	param (
		[string] $computerName
	)
	if (Test-Path -Path ".\TCMSelfTestCS\TCMSelfTestCS\bin\release") {
		Copy-item -Path ".\TCMSelfTestCS\TCMSelfTestCS\bin\release" -Destination "\\$computerName\C$\ETASData\G5HIL\TCMSelfTest\Code"
		Write-Host "SelfTest code copied to $computerName" -ForegroundColor Green
	} else {
		Write-Host "Failed to find SelfTest code in working directory" -ForegroundColor Red
	}
}

function Copy-SelftestFiles {
	param (
		[string] $computerName
	)
	Copy-SelftestUserGuide -$computerName
	copy-SelftestCode -$computerName
}

function Create-iniFile {
	param (
		[string] $computerName
	)
	#TCMSelfTest.ini holds the version number
	New-Item "\\$computerName\C$\ETASData\G5HIL\TCMSelfTest\TCMSelfTest.ini"
	Set-Content "\\$computerName\C$\ETASData\G5HIL\TCMSelfTest\TCMSelfTest.ini" 'VERSION=705'
	if (Test-Path -Path ".\TCMSelfTestCS\TCMSelfTestCS\bin\release") {
		Write-Host "ini file created successfully on $computerName" -ForegroundColor Green
	} else {
		Write-Host "ini file failed to create on $computerName" -ForegroundColor Red
	}
}

foreach ($computer in $selectedComputers) {
	Delete-TCMSelfTestShortcuts -computerName $computer
	Delete-CurrentSelfTestFolder -computerName $computer
	Create-NewSelfTestFolder -computerName $computer
	Copy-SelftestFiles -computerName $computer
	Create-iniFile -computerName $computer
}






Add-Type -AssemblyName PresentationFramework

# Define the list of computers
$computers = @(
  "computerA",
  "computerB",
  "computerC",
  "computerD"
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
        <TextBlock Text="Select computers to install the service on:" Margin="10" />
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

# XAML for the version input dialog
[xml]$versionInputXaml = @"
<Window xmlns="http://schemas.microsoft.com/winfx/2006/xaml/presentation"
        Title="Enter Versions" Height="200" Width="400">
    <Grid>
        <Grid.RowDefinitions>
            <RowDefinition Height="Auto" />
            <RowDefinition Height="Auto" />
            <RowDefinition Height="Auto" />
            <RowDefinition Height="Auto" />
        </Grid.RowDefinitions>
        <TextBlock Text="Enter Version:" Margin="10" Grid.Row="0"/>
        <TextBox Name="VersionTextBox" Margin="10" Grid.Row="1" Width="350"/>
        <TextBlock Text="Enter Required Program Version:" Margin="10" Grid.Row="2"/>
        <TextBox Name="RequiredProgramVersionTextBox" Margin="10" Grid.Row="3" Width="350"/>
        <StackPanel Orientation="Horizontal" HorizontalAlignment="Center" Margin="10" Grid.Row="4">
            <Button Name="VersionOKButton" Content="OK" Width="75" Margin="5" />
            <Button Name="VersionCancelButton" Content="Cancel" Width="75" Margin="5" />
        </StackPanel>
    </Grid>
</Window>
"@

# Load the XAML
$reader = (New-Object System.Xml.XmlNodeReader $xaml)
$window = [Windows.Markup.XamlReader]::Load($reader)

$versionInputReader = (New-Object System.Xml.XmlNodeReader $versionInputXaml)
$versionWindow = [Windows.Markup.XamlReader]::Load($versionInputReader)

# Get the WPF elements
$okButton = $window.FindName("OKButton")
$cancelButton = $window.FindName("CancelButton")
$computerListBox = $window.FindName("ComputerListBox")
$selectAllButton = $window.FindName("SelectAllButton")

$versionOKButton = $versionWindow.FindName("VersionOKButton")
$versionCancelButton = $versionWindow.FindName("VersionCancelButton")
$versionTextBox = $versionWindow.FindName("VersionTextBox")
$requiredProgramVersionTextBox = $versionWindow.FindName("RequiredProgramVersionTextBox")

# Selected computers array
$selectedComputers = New-Object System.Collections.ObjectModel.ObservableCollection[System.String]
$selectAllState = [ref] $false

# Function to close the window and return the selected computers
$okButton.Add_Click({
    $computerListBox.SelectedItems | ForEach-Object {
        $selectedComputers.Add($_.Content)
    }
    if ($selectedComputers.Count -eq 0) {
        [System.Windows.MessageBox]::Show("No computers selected. Exiting...", "Warning", [System.Windows.MessageBoxButton]::OK, [System.Windows.MessageBoxImage]::Warning)
        return
    }

    $versionResult = $versionWindow.ShowDialog()

    if ($versionResult -eq $true) {
        $version = $versionTextBox.Text
        $requiredProgramVersion = $requiredProgramVersionTextBox.Text
        Write-Host "Version: $version"
        Write-Host "Required Program Version: $requiredProgramVersion"
        
        # Proceed with your functions here using the selected computers, version, and required program version
        foreach ($computer in $selectedComputers) {
            Delete-TCMSelfTestShortcuts -computerName $computer
            Delete-CurrentSelfTestFolder -computerName $computer
            Create-NewSelfTestFolder -computerName $computer
            Copy-SelftestFiles -computerName $computer
            Create-iniFile -computerName $computer -version $version
        }
    } else {
        Write-Host "Version input was cancelled."
    }
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

# Function to close the version input window
$versionOKButton.Add_Click({
    $versionWindow.DialogResult = $true
    $versionWindow.Close()
})

$versionCancelButton.Add_Click({
    $versionWindow.DialogResult = $false
    $versionWindow.Close()
})

# Show the main window as a dialog
$window.ShowDialog()

function Delete-TCMSelfTestShortcuts {
    param (
        [string] $computerName
    )
    $networkPublicDesktopPath = "\\$computerName\C$\Users\Public\Desktop"
    
    try {
        $shortcutsToDelete = Get-ChildItem -Path $networkPublicDesktopPath -Filter "TCMSelfTest*.lnk"
        
        foreach ($shortcut in $shortcutsToDelete) {
            Remove-Item -Path $shortcut.FullName -Force
        }
        
        if ($shortcutsToDelete.Count -eq 0) {
            Write-Host "Deleted all TCMSelfTest shortcuts on $computerName" -ForegroundColor Green
        } else {
            Write-Host "Did not delete all TCMSelfTest shortcuts on $computerName" -ForegroundColor Red
        }
    } catch {
        Write-Host "Failed to access or delete TCMSelfTest shortcut on $computerName : $_" -ForegroundColor Red
    }
}

function Delete-CurrentSelfTestFolder {
    param (
        [string] $computerName
    )
    $networkSelftestFolderPath = "\\$computerName\C$\ETASData\G5HIL\TCMSelfTest"
    
    try {
        Remove-Item -Path $networkSelftestFolderPath -Recurse -Force
        if (Test-Path -Path $networkSelftestFolderPath) {
            Write-Host "Did not delete TCMSelfTest on $computerName" -ForegroundColor Red
        } else {
            Write-Host "Deleted TCMSelfTest on $computerName" -ForegroundColor Green
        }
    } catch {
        Write-Host "Failed to access or delete TCMSelfTest folder on $computerName : $_" -ForegroundColor Red
    }
}

function Create-NewSelfTestFolder {
    param (
        [string] $computerName
    )
    # This code only creates the empty folders:
    # C:\ETASData\G5HIL\TCMSelfTest and C:\ETASData\G5HIL\TCMSelfTest\Code
    New-Item -ItemType Directory -Path "\\$computerName\C$\ETASData\G5HIL\TCMSelfTest"
    New-Item -ItemType Directory -Path "\\$computerName\C$\ETASData\G5HIL\TCMSelfTest\Code"
    
    if (Test-Path -Path "\\$computerName\C$\ETASData\G5HIL\TCMSelfTest") {
        Write-Host "TCMSelfTest folder created under C\EtasData\G5HIL on $computerName" -ForegroundColor Green
    } else {
        Write-Host "TCMSelfTest folder failed to create under C\EtasData\G5HIL on $computerName" -ForegroundColor Red
    }
    if (Test-Path -Path "\\$computerName\C$\ETASData\G5HIL\TCMSelfTest\Code") {
        Write

