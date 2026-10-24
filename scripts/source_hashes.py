#!/usr/bin/env python3
"""Record or check the exact Lean source and submission-configuration inputs."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CONFIG = {'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
          'comparator.json', 'formalization.yaml', 'LICENSE', 'NOTICE'}

def fingerprints():
    files = []
    for directory, dirs, names in os.walk(ROOT, followlinks=False):
        dirs[:] = sorted(d for d in dirs if d not in {'.git', '.lake'})
        for name in sorted(names):
            path = Path(directory) / name
            if path.suffix == '.lean' or path.relative_to(ROOT).as_posix() in CONFIG:
                if path.is_symlink():
                    raise SystemExit(f'Source symlink is forbidden: {path}')
                files.append(path)
    return {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(files)}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--output', type=Path)
    mode.add_argument('--check', type=Path)
    args = parser.parse_args()
    current = fingerprints()
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(current, indent=2) + '\n', encoding='utf-8')
        print(f'Recorded {len(current)} source/configuration fingerprints.')
    else:
        recorded = json.loads(args.check.read_text(encoding='utf-8'))
        if current != recorded:
            changed = sorted(k for k in set(current) | set(recorded)
                             if current.get(k) != recorded.get(k))
            raise SystemExit('Source/configuration changed during verification: ' + ', '.join(changed))
        print(f'Confirmed {len(current)} unchanged source/configuration fingerprints.')

if __name__ == '__main__':
    main()
