function Copy-FilesFromFolder {  # This doesn't create the toDestination folder, just moves the files
	param (
		[string] $fromDestination,
		[string] $toDestination
	)
    if (Test-Path -Path $fromDestination) {
        $files = Get-ChildItem -Path "$fromDestination\*" -Recurse
        $totalItems = $files.Count
        $counter = 0
        
        foreach ($item in $files) {
            $counter++
            $percentComplete = ($counter / $totalItems) * 100
            Write-Progress -Activity "Copying files..." -Status "Copying $($item.Name)" -PercentComplete $percentComplete
            Copy-Item -Path $item.FullName -Destination $toDestination -Recurse
        }
        
        # Perform the folder comparison after copying
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
    $fromFiles = Get-ChildItem -Path $fromFolder -File -Recurse | 
                 ForEach-Object { $_.FullName.Substring($fromFolder.Length).TrimStart("\") }
    
    $toFiles = Get-ChildItem -Path $toFolder -File -Recurse | 
               ForEach-Object { $_.FullName.Substring($toFolder.Length).TrimStart("\") }
    
    $differences = Compare-Object -ReferenceObject $fromFiles -DifferenceObject $toFiles
    
    if ($differences) {
        Write-Host "Differences found:" -ForegroundColor Red
        $differences | ForEach-Object {
            Write-Host "$($_.InputObject) - SideIndicator: $($_.SideIndicator)"
        }
        return $false
    } else {
        return $true
    }
}
