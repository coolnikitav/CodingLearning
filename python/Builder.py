function Copy-FilesFromFolder {  
    param (
        [string] $fromDestination,
        [string] $toDestination
    )
    
    if (Test-Path -Path $fromDestination) {
        $items = Get-ChildItem -Path "$fromDestination\*" -Recurse
        $totalItems = $items.Count
        $counter = 0
        
        foreach ($item in $items) {
            $counter++
            
            # Calculate relative path to maintain directory structure
            $relativePath = $item.FullName.Substring($fromDestination.Length).TrimStart("\")
            $destinationPath = Join-Path -Path $toDestination -ChildPath $relativePath
            
            # Update the progress bar
            $percentComplete = ($counter / $totalItems) * 100
            Write-Progress -Activity "Copying files..." -Status "Copying $($item.Name)" -PercentComplete $percentComplete
            
            # Copy the item, maintaining the directory structure
            if ($item.PSIsContainer) {
                # Create the directory in the destination if it doesn't exist
                if (-not (Test-Path -Path $destinationPath)) {
                    New-Item -ItemType Directory -Path $destinationPath -Force
                }
            } else {
                # Copy the file
                Copy-Item -Path $item.FullName -Destination $destinationPath -Force
            }
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

