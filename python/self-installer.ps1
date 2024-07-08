function Delete-FilesStartingWithPrefix {
	param (
		[string] $prefix,
		[string] $address
	)	
	try {
		$shortcutsToDelete = Get-ChildItem -Path $address -Filter "$prefix*.lnk"
		Write-Host "shortcutToDelete: $shortcutsToDelete"
		foreach ($shortcut in $shortcutsToDelete) {
			Remove-Item -Path $shortcut.FullName -Force
		}
			
		$remainingShortcuts = Get-ChildItem -Path $address -Filter "$prefix*.lnk"
		Write-Host "remainingShortcuts: $remainingShortcuts"
		if (!($remainingShortcuts.Count -eq 0)) {
			Write-Host "Failed to delete all $prefix shortcuts" -ForegroundColor Red
			exit
		}
	} catch {
		Write-Host "Failed to access $prefix shortucts : $_" -ForegroundColor Red
		exit
	}
}
