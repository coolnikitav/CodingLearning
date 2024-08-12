function Create-iniFile {
	param (
        [string] $addonsVersion,
		[string] $destination
	)
	#	AddonsVersion.ini holds the version number
    $iniContent = @"
VERSION=$addonsVersion
"@

    Set-Content "$destination\Addons.ini" -Value $iniContent

    if (-not (Test-Path -Path "$destination\Addons.ini")) {
        Write-Host "ini file failed to create" -ForegroundColor Red
		Read-Host -Prompt "Press Enter to exit"
		exit
    }
}
