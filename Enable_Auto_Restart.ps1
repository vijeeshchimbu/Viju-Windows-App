param(
    [string]$TaskName = "VijuTradePCAgent"
)

$ErrorActionPreference = "Stop"

$task = Get-ScheduledTask -TaskName $TaskName -ErrorAction Stop

$settings = New-ScheduledTaskSettingsSet `
    -AllowStartIfOnBatteries `
    -DontStopIfGoingOnBatteries `
    -StartWhenAvailable `
    -MultipleInstances IgnoreNew `
    -RestartCount 255 `
    -RestartInterval (New-TimeSpan -Minutes 1) `
    -ExecutionTimeLimit ([TimeSpan]::Zero)

Set-ScheduledTask -TaskName $TaskName -Settings $settings | Out-Null

$verify = Get-ScheduledTask -TaskName $TaskName
Write-Host ""
Write-Host "VijuTrade PC crash recovery enabled." -ForegroundColor Green
Write-Host "Task:" $TaskName
Write-Host "Restart count:" $verify.Settings.RestartCount
Write-Host "Restart interval:" $verify.Settings.RestartInterval
Write-Host "Start when available:" $verify.Settings.StartWhenAvailable
Write-Host ""
Write-Host "Windows logon auto-start remains enabled."
Write-Host "If the agent crashes, Task Scheduler will retry after 1 minute."
