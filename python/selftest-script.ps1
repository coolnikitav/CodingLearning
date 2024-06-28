Add-Type -AssemblyName PresentationFramework

# Define the list of computers
$computers = @(
    "computerA",
    "computerB",
    "computerC",
    "computerD"
)

# Create the XAML for the GUI
[xml]$HILSelectionXaml = @"
<Window xmlns="http://schemas.microsoft.com/winfx/2006/xaml/presentation"
        Title="Select Computers" Height="725" Width="400">
    <Grid>
        <Grid.RowDefinitions>
            <RowDefinition Height="Auto" />
            <RowDefinition Height="*" />
            <RowDefinition Height="Auto" />
        </Grid.RowDefinitions>
        <TextBlock Text="Select computers to install the service on:" Margin="10" />
        <ListBox Name="HILSelectionComputerListBox" Grid.Row="1" Margin="10" SelectionMode="Multiple">
            $($computers | ForEach-Object { "<ListBoxItem Content='$_' />" })
        </ListBox>
        <StackPanel Grid.Row="2" Orientation="Horizontal" HorizontalAlignment="Center" Margin="10">
            <Button Name="HILSelectionSelectAllButton" Content="Select All" Width="75" Margin="5" />
            <Button Name="HILSelectionOkButton" Content="OK" Width="75" Margin="5" />
            <Button Name="HILSelectionCancelButton" Content="Cancel" Width="75" Margin="5" />
        </StackPanel>
    </Grid>
</Window>
"@

# XAML for the version input dialog
[xml]$selfTestVersionInputXaml = @"
<Window xmlns="http://schemas.microsoft.com/winfx/2006/xaml/presentation"
        Title="Enter Versions" Height="250" Width="300">
    <Grid>
        <Grid.RowDefinitions>
            <RowDefinition Height="Auto" />
            <RowDefinition Height="Auto" />
            <RowDefinition Height="Auto" />
            <RowDefinition Height="Auto" />
            <RowDefinition Height="Auto" />
        </Grid.RowDefinitions>
        <TextBlock Text="Enter SelfTest Version:" Margin="10" Grid.Row="0"/>
        <TextBox Name="selfTestVersionTextBox" Margin="10" Grid.Row="1" Width="250"/>
        <TextBlock Text="Enter Required Acromag Integration Version:" Margin="10" Grid.Row="2"/>
        <TextBox Name="requiredAcromagIntegrationVersionTextBox" Margin="10" Grid.Row="3" Width="250"/>
        <StackPanel Orientation="Horizontal" HorizontalAlignment="Center" Margin="10" Grid.Row="4">
            <Button Name="selfTestVersionOkButton" Content="OK" Width="75" Margin="5" />
            <Button Name="selfTestVersionCancelButton" Content="Cancel" Width="75" Margin="5" />
        </StackPanel>
    </Grid>
</Window>
"@

# Load the HILSelectionXaml
$HILSelectionReader = (New-Object System.Xml.XmlNodeReader $HILSelectionXaml)
$HILSelectionWindow = [Windows.Markup.XamlReader]::Load($HILSelectionReader)

# Display selfTestVersion 
$selfTestVersionInputReader = (New-Object System.Xml.XmlNodeReader $selfTestVersionInputXaml)
$selfTestVersionWindow = [Windows.Markup.XamlReader]::Load($selfTestVersionInputReader)

# Get the WPF elements
$HILSelectionOkButton = $HILSelectionWindow.FindName("HILSelectionOkButton")
$HILSelectionCancelButton = $HILSelectionWindow.FindName("HILSelectionCancelButton")
$HILSelectionComputerListBox = $HILSelectionWindow.FindName("HILSelectionComputerListBox")
$HILSelectionSelectAllButton = $HILSelectionWindow.FindName("HILSelectionSelectAllButton")

$selfTestVersionOKButton = $selfTestVersionWindow.FindName("selfTestVersionOkButton")
$selfTestVersionCancelButton = $selfTestVersionWindow.FindName("selfTestVersionCancelButton")
$selfTestVersionTextBox = $selfTestVersionWindow.FindName("selfTestVersionTextBox")
$requiredAcromagIntegrationVersionTextBox = $selfTestVersionWindow.FindName("requiredAcromagIntegrationVersionTextBox")

# Selected computers array
$selectedComputers = New-Object System.Collections.ObjectModel.ObservableCollection[System.String]
$selectAllState = [ref] $false

# Function to close the window and return the selected computers
$HILSelectionOkButton.Add_Click({
    $HILSelectionComputerListBox.SelectedItems | ForEach-Object {
        $selectedComputers.Add($_.Content)
    }
    $HILSelectionWindow.DialogResult = $true
    $HILSelectionWindow.Close()
})

# Function to close the window without selecting computers
$HILSelectionCancelButton.Add_Click({
    $HILSelectionWindow.DialogResult = $false
    $HILSelectionWindow.Close()
})

# Function to toggle select all / deselect all
$HILSelectionSelectAllButton.Add_Click({
    if ($selectAllState.Value -eq $false) {
        $HILSelectionComputerListBox.SelectAll()
        $HILSelectionSelectAllButton.Content = "Deselect All"
    } else {
        $HILSelectionComputerListBox.UnselectAll()
        $HILSelectionSelectAllButton.Content = "Select All"
    }
    $selectAllState.Value = -not $selectAllState.Value
})

# Function to close the version input window
$selfTestVersionOKButton.Add_Click({
    $selfTestVersionWindow.DialogResult = $true
    $selfTestVersionWindow.Close()
})

$selfTestVersionCancelButton.Add_Click({
    $selfTestVersionWindow.DialogResult = $false
    $selfTestVersionWindow.Close()
})

# Show the HIL selection window and capture the result
$HILSelectionResult = $HILSelectionWindow.ShowDialog()

# Only show the version input window if the HIL selection window was confirmed
if ($HILSelectionResult -eq $true -and $selectedComputers.Count -ne 0) {
    $selfTestVersionResult = $selfTestVersionWindow.ShowDialog()
} else {
    Write-Host "No computers selected or HIL Selection window was cancelled. Exiting..."
    exit
}

if ($selfTestVersionResult -ne $true) {
    Write-Host "Version input was cancelled. Exiting..."
    exit
} else {
    $selfTestVersion = $selfTestVersionTextBox.Text
    $requiredAcromagIntegrationVersion = $requiredAcromagIntegrationVersionTextBox.Text
    Write-Host "Selected computers: $($selectedComputers -join ', ')"
    Write-Host "SelfTest version: $selfTestVersion"
    Write-Host "Required Acromag Integration Version: $requiredAcromagIntegrationVersion"
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
        Write-Host "Code folder created under C\EtasData\G5HIL\TCMSelfTest on $computerName" -ForegroundColor Green
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
        if (Test-Path -Path "\\$computerName\C$\ETASData\G5HIL\TCMSelfTest\TCMSelfTestUserGuide.docx") {
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
        Copy-Item -Path ".\TCMSelfTestCS\TCMSelfTestCS\bin\release\*" -Destination "\\$computerName\C$\ETASData\G5HIL\TCMSelfTest\Code"
        Write-Host "SelfTest code successfully copied to $computerName" -ForegroundColor Green
    } else {
        Write-Host "Failed to find SelfTest code in working directory" -ForegroundColor Red
    }
}

function Copy-SelftestFiles {
    param (
        [string] $computerName
    )
    Copy-SelftestUserGuide -computerName $computerName
    Copy-SelftestCode -computerName $computerName
}

function Create-iniFile {
    param (
        [string] $computerName,
        [string] $selfTestVersion,
        [string] $requiredAcromagIntegrationVersion
    )
    #TCMSelfTest.ini holds the version number
    $iniContent = @"
VERSION=$selfTestVersion
ACROMAG_INTEGRATION_VERSION_REQUIRED=$requiredAcromagIntegrationVersion
"@
    Set-Content "\\$computerName\C$\ETASData\G5HIL\TCMSelfTest\TCMSelfTest.ini" -Value $iniContent

    if (Test-Path -Path "\\$computerName\C$\ETASData\G5HIL\TCMSelfTest\TCMSelfTest.ini") {
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
    Create-iniFile -computerName $computer -selfTestVersion $selfTestVersion -requiredAcromagIntegrationVersion $requiredAcromagIntegrationVersion
}
