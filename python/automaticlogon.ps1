function Compare-Folders {
    param (
        [string] $fromFolder,
        [string] $toFolder
    )
    
    # Get the relative paths of files in the source
    $fromFiles = Get-ChildItem -Path $fromFolder -File -Recurse | 
                 ForEach-Object { $_.FullName.Substring($fromFolder.Length).TrimStart("\") }
    
    # Get the relative paths of files in the destination
    $toFiles = Get-ChildItem -Path $toFolder -File -Recurse | 
               ForEach-Object { $_.FullName.Substring($toFolder.Length).TrimStart("\") }
    
    # Compare the contents, ignoring differences in order
    $differences = Compare-Object -ReferenceObject $fromFiles -DifferenceObject $toFiles
    
    # Output differences
    if ($differences) {
        Write-Host "Differences found:" -ForegroundColor Yellow
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
