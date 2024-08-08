function Copy-FilesFromFolder {
    param (
        [string] $fromDestination,
        [string] $toDestination
    )
    
    if (Test-Path -Path $fromDestination) {
        # Get all files to be copied
        $files = Get-ChildItem -Path "$fromDestination\*" -Recurse
        $totalItems = $files.Count
        $counter = 0
        
        # Loop through the files and folders while copying and updating the progress bar
        foreach ($item in $files) {
            $counter++
            
            # Update progress bar
            $percentComplete = ($counter / $totalItems) * 100
            Write-Progress -Activity "Copying files..." -Status "Copying $($item.Name)" -PercentComplete $percentComplete
            
            # Copy item (file or folder)
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

# Example usage
Copy-FilesFromFolder -fromDestination "C:\SourceFolder" -toDestination "D:\DestinationFolder"
