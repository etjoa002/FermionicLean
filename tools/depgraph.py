"""Print the import graph of the FermionicLean library as an indented list, grouped by layer.

Usage: python tools/depgraph.py            (prints to stdout)
       python tools/depgraph.py --readme   (rewrites the section between the markers in README.md)

A module's line lists the FermionicLean modules it imports directly. Layers follow the
directory structure: Gaussian (real matrices) -> Contraction -> Chain (covariances of chains);
Fock (operators on Fock space) -> Chain/State, Chain/Pure, Chain/KitaevState (the chain as a state).
"""
import os, re, sys
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
SRC = os.path.join(ROOT, 'FermionicLean')
LAYERS = ['Gaussian', 'Contraction', 'Chain', 'Fock']

def modules():
    out = {}
    for dirpath, _, files in os.walk(SRC):
        for f in files:
            if not f.endswith('.lean'):
                continue
            path = os.path.join(dirpath, f)
            name = os.path.relpath(path, ROOT)[:-5].replace(os.sep, '.')
            imps = []
            for line in open(path, encoding='utf-8'):
                m = re.match(r'import\s+(FermionicLean\.[\w.]+)', line)
                if m:
                    imps.append(m.group(1))
            out[name] = imps
    return out

def render(mods):
    lines = []
    for layer in LAYERS:
        names = sorted(n for n in mods if n.startswith('FermionicLean.' + layer + '.'))
        if not names:
            continue
        lines.append('- **%s**' % layer)
        for n in names:
            short = n.split('.', 1)[1]
            deps = ', '.join(sorted(i.split('.', 1)[1] for i in mods[n])) or '(Mathlib only)'
            lines.append('  - `%s` <- %s' % (short, deps))
    return '\n'.join(lines)

if __name__ == '__main__':
    text = render(modules())
    if '--readme' in sys.argv:
        p = os.path.join(ROOT, 'README.md')
        s = open(p, encoding='utf-8').read()
        a, b = '<!-- depgraph:start -->', '<!-- depgraph:end -->'
        i, j = s.index(a) + len(a), s.index(b)
        s = s[:i] + '\n' + text + '\n' + s[j:]
        open(p, 'w', encoding='utf-8').write(s)
        print('README.md updated')
    else:
        print(text)
