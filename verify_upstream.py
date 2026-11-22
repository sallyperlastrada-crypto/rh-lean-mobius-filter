"""Check the pinned source declaration and the independent audit record (stdlib only)."""
from hashlib import sha256
from pathlib import Path
import re
from urllib.request import urlopen


COMMIT = '40e56bab026552e089d7afcfeff08d2defb9c005'
SOURCE = f'https://raw.githubusercontent.com/leanprover-community/riemann-hypothesis/{COMMIT}/'
MIT = 'https://math.mit.edu/~drew/grh/'
AUDIT_SHA = '0a1473fce6eed840011f4a76b1c51558fc6f03edd1e6bd1ee542e6c738d87a62'


def read(url):
    with urlopen(url, timeout=40) as response:
        return response.read()


def main():
    declaration = read(SOURCE + 'src/Main.lean').decode().splitlines()
    if 'theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := allChi' not in declaration:
        raise SystemExit('Unexpected upstream declaration')
    if read(SOURCE + 'lean-toolchain').decode().strip() != 'leanprover/lean4:v4.33.1':
        raise SystemExit('Unexpected upstream toolchain')
    interface = Path(__file__).with_name('SignatureAudit.lean').read_text(encoding='utf-8')
    statements = read(SOURCE + 'src/Statements.lean').decode()
    pattern = r'^def DirichletLNonvanishingRightOfHalf\s*:[^\n]*(?:\n +[^\n]+)+'
    local_def = re.search(pattern, interface, re.M)
    upstream_def = re.search(pattern, statements, re.M)
    if not local_def or not upstream_def or local_def.group().split() != upstream_def.group().split():
        raise SystemExit('Arithmetic interface differs from upstream')
    audit = read(MIT + 'audit.log')
    digest = sha256(audit).hexdigest()
    manifest = read(MIT + 'SHA256SUMS').decode()
    if digest != AUDIT_SHA or not re.search(rf'^{digest}\s+audit\.log$', manifest, re.M):
        raise SystemExit('MIT audit digest mismatch')
    expected = "'LFunction_ne_zero_of_half_lt_re' depends on axioms: [propext, Classical.choice, Quot.sound]"
    if expected not in audit.decode().splitlines():
        raise SystemExit('Missing theorem-specific axiom record')
    print('Verified upstream source pin:', COMMIT)
    print('Verified identical arithmetic interface in SignatureAudit.lean')
    print('Verified external audit SHA-256:', digest)
    print(expected)


if __name__ == '__main__':
    main()
