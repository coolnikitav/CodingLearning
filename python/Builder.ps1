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
