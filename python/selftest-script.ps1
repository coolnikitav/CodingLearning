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
		
		Start-Sleep -Seconds 10  # Wait for all shortcut to get deleted
		
		if ($shortcutsToDelete.Count -eq 0) {
			Write-Host "Deleted all TCMSelfTest shortcuts on $computerName" -ForegroundColor Green
		} else {
			Write-Host "Failed to delete all TCMSelfTest shortcuts on $computerName" -ForegroundColor Red
		}
	} catch {
		Write-Host "Failed to access or delete TCMSelfTest shortuct on $computerName : $_" -ForegroundColor Red
	}
}
