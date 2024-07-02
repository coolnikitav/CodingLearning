# Set the source and destination folders
$sourceFolder = "C:\Source\Files"
$destinationFolder = "C:\Destination\Folder"

# Check if the destination folder already exists
if (Test-Path $destinationFolder) {
  Write-Host "The destination folder already exists."
} else {
  # Create the destination folder
  New-Item -ItemType Directory -Path $destinationFolder
  Write-Host "The destination folder has been created."
}

# Move the files from the source folder to the destination folder
Get-ChildItem -Path $sourceFolder -File | Move-Item -Destination $destinationFolder

# Zip the destination folder
$zipFile = $destinationFolder + ".zip"
Compress-Archive -Path $destinationFolder -DestinationPath $zipFile
Write-Host "The files have been moved and zipped."










function Check-And-Install-PS2EXE {
    param (
        [string]$PS2EXEPath = "C:\Program Files\WindowsPowerShell\Modules\PS2EXE" # Default path, adjust if necessary
    )

    function Show-MessageBox {
        param (
            [string]$message,
            [string]$caption
        )

        Add-Type -AssemblyName PresentationFramework
        $result = [System.Windows.MessageBox]::Show($message, $caption, [System.Windows.MessageBoxButton]::YesNo, [System.Windows.MessageBoxImage]::Question)
        return $result
    }

    if (-Not (Test-Path -Path $PS2EXEPath)) {
        $message = "PS2EXE is not installed. Would you like to install it now?"
        $caption = "Install PS2EXE"
        $result = Show-MessageBox -message $message -caption $caption

        if ($result -eq [System.Windows.MessageBoxResult]::Yes) {
            try {
                Write-Output "Installing PS2EXE..."
                Install-Module -Name PS2EXE -Scope CurrentUser -Force -AllowClobber
                Write-Output "PS2EXE installed successfully."
            } catch {
                Write-Output "Failed to install PS2EXE: $_"
                exit 1
            }
        } else {
            Write-Output "PS2EXE installation declined by user. Exiting script."
            exit 1
        }
    } else {
        Write-Output "PS2EXE is already installed."
    }
}

# Example usage
Check-And-Install-PS2EXE
