#!/usr/bin/env python3
"""Build hash-pinned official Comparator tools in an untracked local cache."""
import argparse
import hashlib
import io
import json
import os
import platform
import shutil
import subprocess
import tarfile
import urllib.request
from pathlib import Path


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def obtain(url, expected, archive):
    if not archive.exists():
        print(f'Downloading {url}', flush=True)
        with urllib.request.urlopen(url, timeout=120) as response:
            with archive.open('wb') as stream:
                shutil.copyfileobj(response, stream)
    if digest(archive) != expected:
        raise ValueError(f'Archive checksum mismatch: {archive}')


def extract(archive, destination, strip=False):
    destination.mkdir(parents=True, exist_ok=True)
    with tarfile.open(archive, 'r:gz') as package:
        for member in package.getmembers():
            if strip:
                parts = Path(member.name).parts[1:]
                if not parts:
                    continue
                member.name = str(Path(*parts))
            package.extract(member, path=destination, filter='data')


def build(cache, lockfile):
    pins = json.loads(lockfile.read_text())
    cache = cache.resolve()
    cache.mkdir(parents=True, exist_ok=True)
    ready = cache / 'READY.json'
    if ready.exists():
        record = json.loads(ready.read_text())
        if record['pins_sha256'] != digest(lockfile):
            raise ValueError('Tool-cache pins changed; select a new cache directory.')
        for tool, entry in record['tools'].items():
            if digest(cache / entry['path']) != entry['sha256']:
                raise ValueError(f'Cached executable changed: {tool}')
        return record
    for name, pin in pins['sources'].items():
        archive = cache / f'{name}-{pin["revision"]}.tar.gz'
        url = f'https://codeload.github.com/{pin["repository"]}/tar.gz/{pin["revision"]}'
        obtain(url, pin['sha256'], archive)
        extract(archive, cache / 'sources' / name, strip=True)
    env = dict(os.environ)
    env['ELAN_TOOLCHAIN'] = pins['toolchain']
    env.update(GOCACHE=str(cache / 'go-build'), GOMODCACHE=str(cache / 'go-mod'),
               GOPATH=str(cache / 'go-path'), GOTOOLCHAIN='local')
    if platform.system() == 'Linux' and platform.machine() in ('x86_64', 'amd64'):
        go_pin = pins['go_linux_amd64']
        archive = cache / 'go-toolchain.tar.gz'
        obtain(go_pin['url'], go_pin['sha256'], archive)
        if not (cache / 'go/bin/go').exists():
            extract(archive, cache)
        go = str(cache / 'go/bin/go')
    else:
        go = shutil.which('go')
        if not go:
            raise ValueError('Install Go >=1.24 on this architecture before bootstrapping Landrun.')
    binary = cache / 'bin'
    binary.mkdir(exist_ok=True)
    with (cache / 'landrun-build.log').open('w') as log:
        subprocess.run([go, 'build', '-mod=readonly', '-o', str(binary / 'landrun'), './cmd/landrun'],
                       cwd=cache / 'sources/landrun', env=env, stdout=log, stderr=log, check=True)
    source = cache / 'sources/comparator'
    lakefile = source / 'lakefile.toml'
    lakefile.write_text(lakefile.read_text().replace('rev = "master"', 'path = "../lean4export"'))
    manifest = source / 'lake-manifest.json'
    data = json.loads(manifest.read_text())
    data['packages'] = [{'type': 'path', 'name': 'lean4export', 'scope': 'leanprover',
                         'dir': '../lean4export', 'manifestFile': 'lake-manifest.json',
                         'inherited': False, 'configFile': 'lakefile.toml'}]
    manifest.write_text(json.dumps(data, indent=2) + '\n')
    with (cache / 'comparator-build.log').open('w') as log:
        subprocess.run(['lake', 'build', 'lean4export', 'comparator'], cwd=source, env=env,
                       stdout=log, stderr=log, check=True)
    for name, path in [('comparator', source / '.lake/build/bin/comparator'),
                       ('lean4export', cache / 'sources/lean4export/.lake/build/bin/lean4export')]:
        shutil.copyfile(path, binary / name)
        (binary / name).chmod(0o755)
    record = {'pins_sha256': digest(lockfile), 'toolchain': pins['toolchain'],
              'tools': {name: {'path': f'bin/{name}', 'sha256': digest(binary / name)}
                        for name in ('comparator', 'lean4export', 'landrun')}}
    ready.write_text(json.dumps(record, indent=2) + '\n')
    print(f'Built pinned tools in {cache}', flush=True)
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cache', type=Path, default=Path(__file__).resolve().parents[2] / '.lake/comparator-tools')
    args = parser.parse_args()
    build(args.cache, Path(__file__).with_name('pins.json'))


if __name__ == '__main__':
    main()
