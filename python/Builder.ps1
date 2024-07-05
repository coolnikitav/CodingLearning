
# Path to the zip file in locationB
$zipFilePath = "C:\Path\To\locationB\YourZipFile.zip"

# Path where the generated script will be saved in locationB
$generatedScriptPath = "C:\Path\To\locationB\scriptB.ps1"

# Read the zip file and convert it to a Base64 string
$zipFileBytes = [System.IO.File]::ReadAllBytes($zipFilePath)
$zipFileBase64 = [System.Convert]::ToBase64String($zipFileBytes)

# Generate scriptB that will embed and install the zip file
$scriptBContent = @"
\$zipFileBase64 = '$zipFileBase64'
\$zipFileBytes = [System.Convert]::FromBase64String(\$zipFileBase64)
\$zipFilePath = 'C:\Path\To\locationC\YourZipFile.zip'

# Write the zip file to locationC
[System.IO.File]::WriteAllBytes(\$zipFilePath, \$zipFileBytes)
Write-Output "Zip file has been installed to \$zipFilePath"
"@

# Write the generated script to the specified path
Set-Content -Path $generatedScriptPath -Value $scriptBContent

Write-Output "ScriptB has been generated at $generatedScriptPath"
