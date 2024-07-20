Add-Type -AssemblyName PresentationFramework

# XAML for the version input dialog
[xml]$selfTestVersionInputXaml = @"
<Window xmlns="http://schemas.microsoft.com/winfx/2006/xaml/presentation"
        Title="Enter Versions" Height="250" Width="400">
    <Grid>
        <Grid.RowDefinitions>
            <RowDefinition Height="Auto" />
            <RowDefinition Height="Auto" />
            <RowDefinition Height="Auto" />
            <RowDefinition Height="Auto" />
            <RowDefinition Height="Auto" />
            <RowDefinition Height="Auto" />
        </Grid.RowDefinitions>
        <Grid.ColumnDefinitions>
            <ColumnDefinition Width="Auto" />
            <ColumnDefinition Width="Auto" />
            <ColumnDefinition Width="Auto" />
            <ColumnDefinition Width="Auto" />
            <ColumnDefinition Width="Auto" />
        </Grid.ColumnDefinitions>

        <TextBlock Text="Enter SelfTest Version:" Margin="10" Grid.Row="0" Grid.ColumnSpan="5"/>
        
        <TextBlock Text="Major:" Margin="10" Grid.Row="1" Grid.Column="0"/>
        <TextBox Name="selfTestVersionMajorTextBox" Margin="10" Grid.Row="1" Grid.Column="1" Width="50"/>
        
        <TextBlock Text="Minor:" Margin="10" Grid.Row="1" Grid.Column="2"/>
        <TextBox Name="selfTestVersionMinorTextBox" Margin="10" Grid.Row="1" Grid.Column="3" Width="50"/>
        
        <TextBlock Text="Patch:" Margin="10" Grid.Row="2" Grid.Column="0"/>
        <TextBox Name="selfTestVersionPatchTextBox" Margin="10" Grid.Row="2" Grid.Column="1" Width="50"/>
        
        <TextBlock Text="Build:" Margin="10" Grid.Row="2" Grid.Column="2"/>
        <TextBox Name="selfTestVersionBuildTextBox" Margin="10" Grid.Row="2" Grid.Column="3" Width="50"/>
        
        <TextBlock Text="Enter Required Acromag Integration Version:" Margin="10" Grid.Row="3" Grid.ColumnSpan="5"/>
        <TextBox Name="requiredAcromagIntegrationVersionTextBox" Margin="10" Grid.Row="4" Grid.ColumnSpan="5" Width="350"/>
        
        <StackPanel Orientation="Horizontal" HorizontalAlignment="Center" Margin="10" Grid.Row="5" Grid.ColumnSpan="5">
            <Button Name="selfTestVersionOkButton" Content="OK" Width="75" Margin="5" />
            <Button Name="selfTestVersionCancelButton" Content="Cancel" Width="75" Margin="5" />
        </StackPanel>
    </Grid>
</Window>
"@

# Display selfTestVersion 
$selfTestVersionInputReader = (New-Object System.Xml.XmlNodeReader $selfTestVersionInputXaml)
$selfTestVersionWindow = [Windows.Markup.XamlReader]::Load($selfTestVersionInputReader)

$selfTestVersionOKButton = $selfTestVersionWindow.FindName("selfTestVersionOkButton")
$selfTestVersionCancelButton = $selfTestVersionWindow.FindName("selfTestVersionCancelButton")
$selfTestVersionMajorTextBox = $selfTestVersionWindow.FindName("selfTestVersionMajorTextBox")
$selfTestVersionMinorTextBox = $selfTestVersionWindow.FindName("selfTestVersionMinorTextBox")
$selfTestVersionPatchTextBox = $selfTestVersionWindow.FindName("selfTestVersionPatchTextBox")
$selfTestVersionBuildTextBox = $selfTestVersionWindow.FindName("selfTestVersionBuildTextBox")
$requiredAcromagIntegrationVersionTextBox = $selfTestVersionWindow.FindName("requiredAcromagIntegrationVersionTextBox")

# Function to close the version input window
$selfTestVersionOKButton.Add_Click({
    $selfTestVersionWindow.DialogResult = $true
    $selfTestVersionWindow.Close()
})

$selfTestVersionCancelButton.Add_Click({
    $selfTestVersionWindow.DialogResult = $false
    $selfTestVersionWindow.Close()
})

$selfTestVersionResult = $selfTestVersionWindow.ShowDialog()

if ($selfTestVersionResult -ne $true) {
    Write-Host "Version input was cancelled. Exiting..."
    exit
} else {
    $selfTestVersionMajor = $selfTestVersionMajorTextBox.Text
    $selfTestVersionMinor = $selfTestVersionMinorTextBox.Text
    $selfTestVersionPatch = $selfTestVersionPatchTextBox.Text
    $selfTestVersionBuild = $selfTestVersionBuildTextBox.Text
    $requiredAcromagIntegrationVersion = $requiredAcromagIntegrationVersionTextBox.Text
    
    $selfTestVersion = "$selfTestVersionMajor.$selfTestVersionMinor.$selfTestVersionPatch.$selfTestVersionBuild"
    $selfTestFolderName = "TCMSelfTest_${selfTestVersionMajor}_${selfTestVersionMinor}_${selfTestVersionPatch}_${selfTestVersionBuild}"
    
    Write-Host "SelfTest version: $selfTestVersion"
    Write-Host "Required Acromag Integration Version: $requiredAcromagIntegrationVersion"
    Write-Host "Folder name: $selfTestFolderName"
}

function Create-NewFolder {
    param (
        [string] $name,
        [string] $destination
    )
    New-Item -ItemType Directory -Path "$destination\$name"  > $null

    if (-not (Test-Path -Path "$destination\$name")) {
        Write-Host "$name folder failed to create" -ForegroundColor Red
    }
}

function Copy-File {
    param (
        [string] $name,
        [string] $fromDestination,
        [string] $toDestination
    )
    if (Test-Path -Path "$name") {
        Copy-Item -Path "$fromDestination\$name" -Destination $toDestination
        if (-not (Test-Path -Path "$toDestination\$name")) {
            Write-Host "$name has failed to copy to $toDestination" -ForegroundColor Red
        }
    } else {
        Write-Host "$name is not found" -ForegroundColor Red
    }
}

function Copy-FilesFromFolder {  # This doesn't create the toDestination folder, just moves the files
    param (
        [string] $fromDestination,
        [string] $toDestination
    )
    if (Test-Path -Path $fromDestination) {
        Copy-item -Path "$fromDestination\*" -Destination $toDestination
        if (-not (Compare-Folders -fromFolder $fromDestination -toFolder $toDestination)) {
            Write-Host "Files failed to copy to $toDestination" -ForegroundColor Red
        }
    } else {
        Write-Host "Failed to find files in $fromDestination" -ForegroundColor Red
    }
}

function Compare-Folders {
    param (
        [string] $fromFolder,
        [string] $toFolder
    )    
    $fromFiles = Get-ChildItem -Path $fromFolder -File -Recurse | ForEach-Object { $_.FullName.Substring($fromFolder.Length).TrimStart("\") }
    $toFiles = Get-ChildItem -Path $toFolder -File -Recurse | ForEach-Object { $_.FullName.Substring($toFolder.Length).TrimStart("\") }
    return Compare-Object -ReferenceObject $fromFiles -DifferenceObject $toFiles
}

function Create-iniFile {
    param (
        [string] $selfTestVersion,
        [string] $requiredAcromagIntegrationVersion,
        [string] $destination
    )
    #TCMSelfTest.ini holds the version number
    $iniContent = @"
VERSION=$selfTestVersion
MINIMUM_ACROMAG_INTEGRATION_VERSION_REQUIRED=$requiredAcromagIntegrationVersion
"@

    Set-Content "$destination\TCMSelfTest.ini" -Value $iniContent

    if (-not (Test-Path -Path "$destination\TCMSelfTest.ini")) {
        Write-Host "ini file failed to create" -ForegroundColor Red
    }
}

function Create-ZipFile {
    param (
        [string] $folderAddress
    )
    $zipFile = $folderAddress + ".zip"
    Compress-Archive -Path $folderAddress -DestinationPath $zipFile
    if (Test-Path -Path "$zipFile") {
        Write-Host "TCMSelfTest_$selfTestVersion has been built successfully" -ForegroundColor Green
    } else {
        Write-Host "TCMSelfTest_$selfTestVersion has failed to build" -ForegroundColor Red
    }
}

function Delete-Folder {
    param (
        [string] $name,
        [string] $address
    )    
    try {
        Remove-Item -Path "$address\$name" -Recurse -Force
    } catch {
        Write-Host "Failed to access $name folder : $_" -ForegroundColor Red
    }
}

$TCMSelfTestInstallersAddress = "\\corp.alsn.com\proddfs\Controls\Application_Installers\ETAS_Simulation\TCMSelfTestInstallers"

function Build-Selftest {
    if (Test-Path "$TCMSelfTestInstallersAddress\$selfTestFolderName") {
        Write-Host "The $selfTestVersion version already exists. Builder will exit now..." -ForegroundColor Red
        exit
    }
    Create-NewFolder -name "$self
