function Unzip-ZipFile {
    param (
        [string] $zipName,
        [string] $zipLocation,
        [string] $destination,
        [string[]] $excludeFolders = @()  # Default to an empty array
    )

    # Check if the zip file exists
    if (Test-Path -Path "$zipLocation\$zipName") {
        Add-Type -AssemblyName 'System.IO.Compression.FileSystem'
        $zip = [System.IO.Compression.ZipFile]::OpenRead("$zipLocation\$zipName")
        
        foreach ($entry in $zip.Entries) {
            $exclude = $false

            # Check if the current entry is in one of the excluded folders
            foreach ($folder in $excludeFolders) {
                if ($entry.FullName -like "$folder/*" -or $entry.FullName -like "$folder/") {
                    $exclude = $true
                    break
                }
            }

            # Extract only if the entry is not in an excluded folder
            if (-not $exclude) {
                $entryPath = Join-Path $destination $entry.FullName
                $entryDir = Split-Path $entryPath -Parent

                if (-not (Test-Path $entryDir)) {
                    New-Item -ItemType Directory -Path $entryDir | Out-Null
                }
                
                $entry.ExtractToFile($entryPath, $true)
            }
        }

        $zip.Dispose()
        
        # Delete zipFile after unzipping it
        Remove-Item -Path "$zipLocation\$zipName" -Force
    } else {
        Write-Host "$zipName is not found" -ForegroundColor Red
        Read-Host -Prompt "Press Enter to exit"
        exit
    }
}
