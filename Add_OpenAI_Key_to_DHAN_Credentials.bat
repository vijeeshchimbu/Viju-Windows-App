@echo off
setlocal EnableExtensions
title Viju_Trade - Add OpenAI API Key to DHAN Credentials

set "VIJU_DIR=%USERPROFILE%\NiftyMonitor"
set "SECRETS=%VIJU_DIR%\.secrets.env"
set "BROKER=%VIJU_DIR%\broker_selection.json"

if not exist "%VIJU_DIR%" mkdir "%VIJU_DIR%"

echo.
echo Viju_Trade DHAN Credentials
echo ---------------------------
echo This updates OPENAI_API_KEY only.
echo Existing DHAN credentials are preserved.
echo.

powershell -NoProfile -ExecutionPolicy Bypass -Command ^
  "$ErrorActionPreference='Stop';" ^
  "$path=$env:SECRETS;" ^
  "$secure=Read-Host 'Paste OpenAI API key' -AsSecureString;" ^
  "$bstr=[Runtime.InteropServices.Marshal]::SecureStringToBSTR($secure);" ^
  "try{$key=[Runtime.InteropServices.Marshal]::PtrToStringBSTR($bstr)}finally{[Runtime.InteropServices.Marshal]::ZeroFreeBSTR($bstr)};" ^
  "if([string]::IsNullOrWhiteSpace($key)){throw 'OpenAI API key cannot be empty'};" ^
  "$lines=@(); if(Test-Path -LiteralPath $path){$lines=Get-Content -LiteralPath $path -Encoding UTF8};" ^
  "$out=New-Object System.Collections.Generic.List[string]; $done=$false;" ^
  "foreach($line in $lines){if($line -match '^\s*OPENAI_API_KEY\s*='){if(-not $done){$out.Add('OPENAI_API_KEY='+$key);$done=$true}}else{$out.Add($line)}};" ^
  "if(-not $done){$out.Add('OPENAI_API_KEY='+$key)};" ^
  "[IO.File]::WriteAllLines($path,$out,[Text.UTF8Encoding]::new($false));" ^
  "$broker=$env:BROKER; [IO.File]::WriteAllText($broker,'{"schema":2,"broker_selected":"DHAN","selection_id":"windows-dhan"}',[Text.UTF8Encoding]::new($false));"

if errorlevel 1 (
    echo.
    echo FAILED to save the OpenAI API key.
    pause
    exit /b 1
)

icacls "%SECRETS%" /inheritance:r /grant:r "%USERNAME%:F" >nul 2>&1
icacls "%BROKER%" /inheritance:r /grant:r "%USERNAME%:F" >nul 2>&1

echo.
echo SUCCESS.
echo OPENAI_API_KEY was added/updated in:
echo %SECRETS%
echo.
echo Your existing DHAN credentials were not changed.
pause
