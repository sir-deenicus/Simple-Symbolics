# IncrementVersion.ps1
param (
    [string]$projectFile
)

if (-not $projectFile) {
    Write-Error "Please provide the project file path."
    exit 1
}

# Load the XML
[xml]$xml = Get-Content $projectFile

# Find the Version element
$version = $xml.Project.PropertyGroup.Version

# Split the version into parts
$versionParts = $version -split '\.'

$oldver = $versionParts[0] + "." + $versionParts[1] + "." + $versionParts[2]

# Convert parts to integers
$major = [int]$versionParts[0]
$minor = [int]$versionParts[1]
$patch = [int]$versionParts[2]

# Increment the patch version
$patch++
if ($patch -gt 9) {
    $patch = 0
    $minor++
    if ($minor -gt 9) {
        $minor = 0
        $major++
    }
}

# Update the version
$newVersion = "$major.$minor.$patch"

# Update the version element 
# Find the Version element
$versionElement = $xml.SelectSingleNode("//Version")

if ($null -eq $versionElement) {
    Write-Error "Version element not found in the project file."
    exit 1
}

$versionElement.InnerText = $newVersion

$version2 = $xml.Project.PropertyGroup.Version
 
# Save the updated XML back to the project file
$xml.Save($projectFile)
$fileName = Split-Path $projectFile -Leaf
Write-Output "$fileName version updated from $oldver to $version2"
