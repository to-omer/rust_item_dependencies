$ErrorActionPreference = 'Stop'
$PSNativeCommandUseErrorActionPreference = $false

$stdout = Join-Path $env:RUNNER_TEMP 'rid-wsl-docker.stdout.log'
$stderr = Join-Path $env:RUNNER_TEMP 'rid-wsl-docker.stderr.log'
# Keep the foreground WSL session alive through the Actions' post-job cleanup.
# The runner reaps this child using its inherited RUNNER_TRACKING_ID afterwards.
$daemon = Start-Process -FilePath 'wsl.exe' -PassThru -WindowStyle Hidden `
    -RedirectStandardOutput $stdout -RedirectStandardError $stderr `
    -ArgumentList @('--distribution', 'Ubuntu-24.04', '--user', 'root', '--exec',
        '/usr/bin/dockerd', '--host=unix:///var/run/docker.sock',
        '--host=tcp://127.0.0.1:2375', '--tls=false')
$env:DOCKER_HOST = 'tcp://127.0.0.1:2375'
$deadline = [DateTime]::UtcNow.AddSeconds(60)
try {
    while ([DateTime]::UtcNow -lt $deadline) {
        if ($daemon.HasExited) {
            throw "WSL Docker daemon exited with code $($daemon.ExitCode)"
        }
        $osType = docker info --format '{{.OSType}}'
        if ($LASTEXITCODE -eq 0) {
            if ($osType.Trim() -ne 'linux') {
                throw "Expected a Linux Docker daemon, got: $osType"
            }
            "DOCKER_HOST=$env:DOCKER_HOST" >> $env:GITHUB_ENV
            docker version
            if ($LASTEXITCODE -ne 0) { throw 'Could not read Docker version' }
            exit 0
        }
        Start-Sleep -Seconds 1
    }
    throw 'WSL Docker daemon did not become ready within 60 seconds'
} catch {
    Get-Content $stdout, $stderr
    throw
}
