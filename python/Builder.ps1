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

function Get-PS2EXEPath {
	# Get the path to the PS2EXE module in the current user's profile
	return Join-Path -Path $env:USERPROFILE -ChildPath "Documents\WindowsPowerShell\Modules\PS2EXE"
}

$ps2exePath = Get-PS2EXEPath

# PS2EXE tool is needed to convert powershell script to executable
function Check-And-Install-PS2EXE {
    function Show-MessageBox {
        param (
            [string]$message,
            [string]$caption
        )

        Add-Type -AssemblyName PresentationFramework
        $result = [System.Windows.MessageBox]::Show($message, $caption, [System.Windows.MessageBoxButton]::YesNo, [System.Windows.MessageBoxImage]::Question)
        return $result
    }

    if (-Not (Test-Path -Path $ps2exePath)) {
        $message = "PS2EXE is not installed. It is needed to generate the executable. Would you like to install it now?"
        $caption = "Install PS2EXE"
        $result = Show-MessageBox -message $message -caption $caption

        if ($result -eq [System.Windows.MessageBoxResult]::Yes) {
            try {
                Write-Output "Installing PS2EXE..."
                Install-Module -Name PS2EXE -Scope CurrentUser -Force -AllowClobber
                Write-Output "PS2EXE installed successfully."
            } catch {
                Write-Output "Failed to install PS2EXE: $_"
                exit 1
            }
        } else {
            Write-Output "PS2EXE installation declined by user. Exiting script."
            exit 1
        }
    } else {
        Write-Output "PS2EXE is already installed."
    }
}

function Create-NewFolder {
	param (
		[string] $name,
		[string] $destination
	)
	New-Item -ItemType Directory -Path "$destination\$name"
	
	if (Test-Path -Path "$destination\$name") {
		Write-Host "$name folder created" -ForegroundColor Green
	} else {
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
		if (Test-Path -Path "$toDestination\$name") {
			Write-Host "$name has been copied to $toDestination" -ForegroundColor Green
		} else {
			Write-Host "$name has failed been to copy to $toDestination" -ForegroundColor Red
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
		if (Check-CopiedFiles -fromFolder $fromDestination -toFolder $toDestination) {
			#Write-Host "Files successfully copied to $toDestination" -ForegroundColor Green
		} else {
			#Write-Host "Files failed to copy to $toDestination" -ForegroundColor Red
		}
	} else {
		Write-Host "Failed to find files in $fromDestination" -ForegroundColor Red
	}
}

function Check-CopiedFiles {
	param (
		[string] $fromFolder,
		[string] $toFolder
	)	
	$fromFiles = Get-ChildItem -Path $fromFolder -File -Recurse
	$toFiles = Get-ChildItem -Path $toFolder -File -Recurse
	
	return Compare-Object -ReferenceObject $fromFiles -DifferenceObject $toFiles -Property Name, Length, LastWriteTime -SyncWindow 0
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

    if (Test-Path -Path "$destination\TCMSelfTest.ini") {
        Write-Host "ini file created successfully" -ForegroundColor Green
    } else {
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

function Unzip-ZipFile {
	param (
		[string] $zipName,
		[string] $zipLocation,
		[string] $destination
	)
	Expand-Archive -Path "$zipLocation\$zipName" -DestinationPath $destination -Force
}

function Delete-FilesStartingWithPrefix {
	param (
		[string] $prefix,
		[string] $address
		
	)	
	try {
		$shortcutsToDelete = Get-ChildItem -Path $address -Filter "$prefix*.lnk"
		
		foreach ($shortcut in $shortcutsToDelete) {
			Remove-Item -Path $shortcut.FullName -Force
		}
			
		$remainingShortcuts = Get-ChildItem -Path $address -Filter "$prefix*.lnk"
		
		if ($remainingShortcuts.Count -eq 0) {
			Write-Host "Deleted all $prefix shortcuts" -ForegroundColor Green
		} else {
			Write-Host "Failed to delete all $prefix shortcuts" -ForegroundColor Red
		}
	} catch {
		Write-Host "Failed to access $prefix shortucts : $_" -ForegroundColor Red
	}
}

function Delete-Folder {
	param (
		[string] $name,
		[string] $address
	)	
	try {
		Remove-Item -Path "$address\$name" -Recurse -Force
		if (Test-Path -Path "$address\$name") {
			Write-Host "Did not delete $name" -ForegroundColor Red
		} else {
			Write-Host "Deleted $name" -ForegroundColor Green
		}
	} catch {
		Write-Host "Failed to access $name folder : $_" -ForegroundColor Red
	}
}

function Create-Shortcut {
	param (
		[string] $name,
		[string] $location,
		[string] $targetPath
	)
	$WScriptShell = New-Object -ComObject WScript.Shell
	$shortcut = $WScriptShell.CreateShortcut($location)
	$shortcut.TargetPath = $targetPath
	$shortcut.Save()
}

# This function is used to create the self installer from the zip file
# Self installer can be copied to other machines and ran manually
# This can be needed if someone who doesn't have access to Synergy and the installer script needs to install
function Create-Exe {
	param (
		[string] $zipName,
		[string] $exeName,
		[string] $installerPath,
		[string] $destination  # When exe is ran this is where it will unzip the files to
	)
	# This is what the executable will do
	$scriptContent = @"
		Delete-FilesStartingWithPrefix -prefix "TCMSelfTest" -address "C:\Users\Public\Desktop"
		Delete-Folder -name "TCMSelfTest" -address "C:\ETASData\G5HIL"
		Unzip-ZipFile -zipName "TCMSelfTest_$selfTestVersion" -zipLocation $TCMSelfTestInstallersAddress -destination "C:\ETASData\G5HIL"
		Create-Shortcut -name "TCMSelfTest" -location "C:\Users\Public\Desktop" -targetPath "C:\ETASData\G5HIL\TCMSelfTest\Code\TCMSelfTestCS.exe
"@

	Set-Content -Path "$installerPath\$exeName" -Value $scriptContent
	
	
}

$TCMSelfTestInstallersAddress = "\\corp.alsn.com\proddfs\Controls\Application_Installers\ETAS_Simulation\TCMSelfTestInstallers"

function Build-Selftest {
	if (Test-Path "$TCMSelfTestInstallersAddress\TCMSelfTest_$selfTestVersion") {
	  Write-Host "The $selfTestVersion version already exists. Builder will exit now..." -ForegroundColor Red
	  exit
	}
	Check-And-Install-PS2EXE
	Create-NewFolder -name "TCMSelfTest_$selfTestVersion" -destination $TCMSelfTestInstallersAddress
	Create-NewFolder -name "TCMSelfTest" -destination "$TCMSelfTestInstallersAddress\TCMSelfTest_$selfTestVersion"
	Create-NewFolder -name "Code" -destination "$TCMSelfTestInstallersAddress\TCMSelfTest_$selfTestVersion\TCMSelfTest"
	Copy-File -name "TCMSelfTestUserGuide.docx" -fromDestination ".\" -toDestination "$TCMSelfTestInstallersAddress\TCMSelfTest_$selfTestVersion\TCMSelfTest"
	Copy-FilesFromFolder -fromDestination ".\TCMSelfTestCS\TCMSelfTestCS\bin\release" -toDestination "$TCMSelfTestInstallersAddress\TCMSelfTest_$selfTestVersion\TCMSelfTest\Code"
	Check-CopiedFiles -fromFolder ".\TCMSelfTestCS\TCMSelfTestCS\bin\release" -toFolder "$TCMSelfTestInstallersAddress\TCMSelfTest_$selfTestVersion\TCMSelfTest\Code"
	Create-iniFile -selfTestVersion $selfTestVersion -requiredAcromagIntegrationVersion $requiredAcromagIntegrationVersion -destination "$TCMSelfTestInstallersAddress\TCMSelfTest_$selfTestVersion\TCMSelfTest"
	Create-ZipFile -folderAddress "$TCMSelfTestInstallersAddress\TCMSelfTest_$selfTestVersion"
	#Create-ExeFromZip -zipName "TCMSelfTest_$selfTestVersion" -exeName ("TCMSelfTest_" + $selfTestVersion + "_installer") -zipPath $TCMSelfTestInstallersAddress -destination "C:\ETASData\G5HIL"
}

Build-Selftest
