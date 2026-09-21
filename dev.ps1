# Start backend (Flask) + frontend (Vite) together in this console.
# Ctrl+C (or closing the window) stops both.
$ErrorActionPreference = 'Stop'
$root = $PSScriptRoot

$py = Start-Process python -ArgumentList '-m', 'backend' -WorkingDirectory $root -NoNewWindow -PassThru
$npm = Start-Process npm.cmd -ArgumentList 'run', 'dev' -WorkingDirectory (Join-Path $root 'frontend') -NoNewWindow -PassThru

Write-Host ''
Write-Host "holpy dev: backend PID $($py.Id), frontend PID $($npm.Id)"
Write-Host 'Open http://localhost:8080  (Ctrl+C stops both)'

$py.WaitForExit()
$npm.WaitForExit()