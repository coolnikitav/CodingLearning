Add-Type -AssemblyName PresentationFramework

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

# Display selfTestVersion 
$selfTestVersionInputReader = (New-Object System.Xml.XmlNodeReader $selfTestVersionInputXaml)
$selfTestVersionWindow = [Windows.Markup.XamlReader]::Load($selfTestVersionInputReader)

$selfTestVersionOKButton = $selfTestVersionWindow.FindName("selfTestVersionOkButton")
$selfTestVersionCancelButton = $selfTestVersionWindow.FindName("selfTestVersionCancelButton")
$selfTestVersionTextBox = $selfTestVersionWindow.FindName("selfTestVersionTextBox")
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
    $selfTestVersion = $selfTestVersionTextBox.Text
	$requiredAcromagIntegrationVersion = $requiredAcromagIntegrationVersionTextBox.Text
    Write-Host "SelfTest version: $selfTestVersion"
	Write-Host "Required Acromag Integration Version: $requiredAcromagIntegrationVersion"
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
	if (Test-Path "$TCMSelfTestInstallersAddress\TCMSelfTest_$selfTestVersion") {
	  Write-Host "The $selfTestVersion version already exists. Builder will exit now..." -ForegroundColor Red
	  exit
	}
	Create-NewFolder -name "TCMSelfTest_$selfTestVersion" -destination $TCMSelfTestInstallersAddress
	Create-NewFolder -name "Code" -destination "$TCMSelfTestInstallersAddress\TCMSelfTest_$selfTestVersion"
	Copy-File -name "TCMSelfTestUserGuide.docx" -fromDestination ".\" -toDestination "$TCMSelfTestInstallersAddress\TCMSelfTest_$selfTestVersion"
	Copy-FilesFromFolder -fromDestination ".\TCMSelfTestCS\TCMSelfTestCS\bin\release" -toDestination "$TCMSelfTestInstallersAddress\TCMSelfTest_$selfTestVersion\Code"
	Create-iniFile -selfTestVersion $selfTestVersion -requiredAcromagIntegrationVersion $requiredAcromagIntegrationVersion -destination "$TCMSelfTestInstallersAddress\TCMSelfTest_$selfTestVersion"
	Create-ZipFile -folderAddress "$TCMSelfTestInstallersAddress\TCMSelfTest_$selfTestVersion"
	Delete-Folder -name "TCMSelfTest_$selfTestVersion" -address $TCMSelfTestInstallersAddress
}

Build-Selftest

Read-Host -Prompt "Press Enter to exit"
