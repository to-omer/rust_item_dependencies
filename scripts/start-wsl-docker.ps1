$ErrorActionPreference = 'Stop'
$PSNativeCommandUseErrorActionPreference = $false

# Keep ShellExecute enabled: Windows-side redirection inherits the runner's pipes,
# causing its process invoker to kill this child when the setup step exits.
# The runner reaps the independent WSL session after the Actions' post-job cleanup.
$daemon = Start-Process -FilePath 'wsl.exe' -PassThru -WindowStyle Hidden `
    -ArgumentList @('--distribution', 'Ubuntu-24.04', '--user', 'root', '--exec',
        '/bin/sh', '-c', '"exec /usr/bin/dockerd --host=unix:///var/run/docker.sock --host=tcp://127.0.0.1:2375 --tls=false >/var/log/rid-docker.log 2>&1"')
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
            "RID_WSL_DOCKER_PID=$($daemon.Id)" >> $env:GITHUB_ENV
            docker version
            if ($LASTEXITCODE -ne 0) { throw 'Could not read Docker version' }
            exit 0
        }
        Start-Sleep -Seconds 1
    }
    throw 'WSL Docker daemon did not become ready within 60 seconds'
} catch {
    wsl --distribution Ubuntu-24.04 --user root --exec tail -n 200 /var/log/rid-docker.log
    throw
}
