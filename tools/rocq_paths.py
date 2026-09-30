"""The two source roots compiled by the root dune build.

Installed mathematics lives in theories/ (PTree); standalone compilation
clients live in tests/ (PTree.Tests). Audits must inspect both roots.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE_ROOTS = (('theories', ''), ('tests', 'Tests/'))
LOADPATH = ['-R', '_build/default/theories', 'PTree',
            '-R', '_build/default/tests', 'PTree.Tests']


def source_files(root=ROOT):
    return sorted(p for directory, _ in SOURCE_ROOTS
                  for p in (root / directory).rglob('*.v'))


def module_key(path, root=ROOT):
    relative = path.relative_to(root)
    for directory, prefix in SOURCE_ROOTS:
        if relative.parts[0] == directory:
            return prefix + Path(*relative.parts[1:]).with_suffix('').as_posix()
    raise ValueError('Not a Rocq source: ' + str(path))


def source_path(module, root=ROOT):
    if module.startswith('Tests/'):
        return root / 'tests' / (module.removeprefix('Tests/') + '.v')
    return root / 'theories' / (module + '.v')
