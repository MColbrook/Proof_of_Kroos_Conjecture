# Native Windows preparation only. Full sandboxed verification requires Linux.
param([switch]$BuildOnly)
$ErrorActionPreference = 'Stop'
$repositoryRoot = Split-Path -Parent $PSScriptRoot
Push-Location -LiteralPath $repositoryRoot
try {
    python scripts/audit.py
    if ($LASTEXITCODE -ne 0) { throw 'Source-package audit failed.' }
    if (-not $BuildOnly) {
        throw 'Full verification requires Linux and bubblewrap. Run bash scripts/verify.sh in a Linux checkout or GitHub Actions. Native Windows build only: explicitly pass -BuildOnly; this does not perform Comparator or independent kernel replay.'
    }
    lake exe cache get
    if ($LASTEXITCODE -ne 0) { throw 'Mathlib cache retrieval failed.' }
    lake build
    if ($LASTEXITCODE -ne 0) { throw 'Lean build failed.' }
    lake env lean AxiomReport.lean
    if ($LASTEXITCODE -ne 0) { throw 'Axiom report failed.' }
    lake env lean NumericalBounds.lean
    if ($LASTEXITCODE -ne 0) { throw 'Numerical bounds check failed.' }
    Write-Host 'Windows Lean build and source audit passed. Sandboxed Comparator and independent kernel replay have not run.'
}
finally {
    Pop-Location
}
