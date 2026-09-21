"""Read-only CI version check; the opam constraint package owns the versions."""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PROFILE = ROOT / '.github/ci/ptree-ci.opam'


def profile_versions(text):
    block = text.split('depends: [', 1)[1].split(']', 1)[0]
    versions = {}
    for line in block.splitlines():
        if not line.strip():
            continue
        match = re.fullmatch(r'\s*"([\w+-]+)"\s*\{= "([\w.+~-]+)"\}\s*', line)
        if not match:
            raise ValueError(f'Not an exact package constraint: {line}')
        name, version = match.groups()
        if name in versions:
            raise ValueError(f'Duplicate package constraint: {name}')
        versions[name] = version
    if not versions:
        raise ValueError('Empty CI profile')
    return versions


def installed_versions(text):
    versions = {}
    for line in text.splitlines():
        if not line.strip() or line.startswith('#'):
            continue
        name, version = line.split()
        if name in versions:
            raise ValueError(f'Duplicate installed package: {name}')
        versions[name] = version
    return versions


def check_versions(expected, actual):
    errors = [f'{name}: expected {version}, got {actual.get(name, "MISSING")}'
              for name, version in expected.items() if actual.get(name) != version]
    # conf-* packages probe OS libraries; Linux can need probes absent on macOS.
    extras = set(actual) - set(expected) - {'ptree-ci', 'coq-ptree'}
    errors += [f'Unfrozen dependency: {name}' for name in sorted(extras)
               if not name.startswith('conf-')]
    if errors:
        raise ValueError('\n'.join(errors))


def output(*args):
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


def main():
    frontend = output('opam', '--version')
    if frontend != '2.5.1':
        raise ValueError(f'Unexpected opam frontend: {frontend}; expected 2.5.1')
    expected = profile_versions(PROFILE.read_text())
    actual = installed_versions(output('opam', 'list', '--installed', '--columns=name,version',
                                       '--color=never'))
    check_versions(expected, actual)
    for command, version in [('ocamlc', expected['ocaml']), ('dune', expected['dune'])]:
        flag = '-version' if command == 'ocamlc' else '--version'
        found = output('opam', 'exec', '--', command, flag)
        if found != version:
            raise ValueError(f'{command} executable: expected {version}, got {found}')
    coq = output('opam', 'exec', '--', 'coqc', '--version')
    if f'version {expected["coq"]}\n' not in coq + '\n':
        raise ValueError(f'Unexpected Coq executable: {coq}')
    print(f'Frozen profile verified: {len(expected)} exact package versions.')
    print(coq)
    print('opam:', frontend)
    print('OS-specific probes:', ', '.join(sorted(set(actual) - set(expected) -
                                                {'ptree-ci', 'coq-ptree'})) or 'none')


if __name__ == '__main__':
    main()
