"""Fetch the eight pinned Alpöge–Claude source modules used by the one-sided proof."""
import hashlib
import json
from pathlib import Path
import re
import urllib.request


def main():
    root = Path(__file__).resolve().parent
    manifest = json.loads((root/'upstream.json').read_text(encoding='utf-8'))
    pin = manifest['commit']
    if pin != '40e56bab026552e089d7afcfeff08d2defb9c005':
        raise SystemExit('Unexpected upstream pin')
    modules = {m['module'] for m in manifest['modules']}
    for entry in manifest['modules']:
        name = entry['module']
        if not re.fullmatch(r'Formalism(?:\.\w+)+', name):
            raise SystemExit('Invalid module name')
        path = name.replace('.', '/') + '.lean'
        dest = root/'.lake/landau-src'/path
        if dest.is_file() and hashlib.sha256(dest.read_bytes()).hexdigest() == entry['sha256']:
            continue
        url = f'https://raw.githubusercontent.com/leanprover-community/riemann-hypothesis/{pin}/src/{path}'
        with urllib.request.urlopen(url, timeout=45) as r:
            data = r.read()
        if hashlib.sha256(data).hexdigest() != entry['sha256']:
            raise SystemExit(f'Source checksum mismatch for {name}')
        if any(i != 'Mathlib' and i not in modules for i in entry['imports']):
            raise SystemExit(f'Unexpected dependency of {name}')
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(data)
    print(f'Checked {len(modules)} pinned modules.')


if __name__ == '__main__':
    main()
