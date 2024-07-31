function Copy-FilesFromFolder {  # This doesn't create the toDestination folder, just moves the files
	param (
		[string] $fromDestination,
		[string] $toDestination
	)
	if (Test-Path -Path $fromDestination) {
		Copy-item -Path "$fromDestination\*" -Destination $toDestination -Recurse
		if (-not (Compare-Folders -fromFolder $fromDestination -toFolder $toDestination)) {
			Write-Host "Files failed to copy to $toDestination" -ForegroundColor Red
			Read-Host -Prompt "Press Enter to exit"
			exit
		}
	} else {
		Write-Host "Failed to find files in $fromDestination" -ForegroundColor Red
		Read-Host -Prompt "Press Enter to exit"
		exit
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
