function Unzip-ZipFile {
    param (
        [string] $zipName,
        [string] $zipLocation,
        [string] $destination,
        [string[]] $excludeFolders = @()  # Default to an empty array
    )

    # Check if the zip file exists
    if (Test-Path -Path "$zipLocation\$zipName") {
        # Use Expand-Archive to unzip the entire file
        Expand-Archive -Path "$zipLocation\$zipName" -DestinationPath $destination -Force

        # Remove the excluded folders
        foreach ($folder in $excludeFolders) {
            $folderPath = Join-Path $destination $folder
            if (Test-Path -Path $folderPath) {
                Remove-Item -Path $folderPath -Recurse -Force
            }
        }

        # Optionally, delete the original zip file after extraction
        Remove-Item -Path "$zipLocation\$zipName" -Force
    } else {
        Write-Host "$zipName is not found" -ForegroundColor Red
        Read-Host -Prompt "Press Enter to exit"
        exit
    }
}
