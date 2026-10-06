#!/usr/bin/env python3
"""Run official Comparator with real Landrun and systemd AF_UNIX restrictions."""
import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

from bootstrap import build


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--cache', type=Path)
    parser.add_argument('--config', type=Path)
    args = parser.parse_args()
    project = args.project.resolve()
    cache = (args.cache or project / '.lake/comparator-tools').resolve()
    config = (args.config or Path(__file__).with_name('comparator.json')).resolve()
    pins = Path(__file__).with_name('pins.json')
    record = build(cache, pins)
    if (project / 'lean-toolchain').read_text().strip() != record['toolchain']:
        raise ValueError('Project toolchain differs from pinned Comparator toolchain.')
    env = dict(os.environ)
    env['ELAN_TOOLCHAIN'] = record['toolchain']
    env['COMPARATOR_LANDRUN'] = str(cache / record['tools']['landrun']['path'])
    env['COMPARATOR_LEAN4EXPORT'] = str(cache / record['tools']['lean4export']['path'])
    env['PATH'] = subprocess.check_output(['lake', 'env', 'printenv', 'PATH'], cwd=project, env=env, text=True).strip()
    command = ['systemd-run', '--user', '--wait', '--pipe',
               '--property=RestrictAddressFamilies=~AF_UNIX', '--working-directory=' + str(project)]
    for key in ('PATH', 'HOME', 'ELAN_TOOLCHAIN', 'COMPARATOR_LANDRUN', 'COMPARATOR_LEAN4EXPORT'):
        command.extend(['--setenv', key + '=' + env[key]])
    command.extend(['lake', 'env', str(cache / record['tools']['comparator']['path']), str(config)])
    result = subprocess.run(command, cwd=project, env=env)
    return result.returncode


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f'Comparator setup failed: {error}', file=sys.stderr)
        sys.exit(1)
