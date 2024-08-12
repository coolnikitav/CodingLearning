function Unzip-ZipFile {
	param (
		[string] $zipName,
		[string] $zipLocation,
		[string] $destination
	)
	if (Test-Path -Path "$zipLocation\$zipName") {
		Expand-Archive -Path "$zipLocation\$zipName" -DestinationPath $destination -Force
	} else {
		Write-Host "$zipName is not found" -ForegroundColor Red
		Read-Host -Prompt "Press Enter to exit"
		exit
	}
	
	# Delete zipFile after unzipping it
	Remove-Item -Path "$destination\$zipName" -Force
}
