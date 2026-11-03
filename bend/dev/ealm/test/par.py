import subprocess, sys, os, concurrent.futures as cf
# usage: par.py BIN PROGS ORACLE... ; compares the Bend harness to the oracle blocks
binp, progsf = sys.argv[1], sys.argv[2]
progs = [l.replace('\\n', '\n') for l in open(progsf).read().split('\n') if l]
blocks = []
for of in sys.argv[3:]:
    cur = None
    for line in open(of).read().split('\n'):
        if line.startswith('== '):
            if cur is not None: blocks.append(cur)
            cur = [line]
        elif cur is not None: cur.append(line)
    if cur is not None: blocks.append(cur)
def norm(b):
    out = []; seen = False
    for l in b:
        if l.startswith('main:') or l.startswith('parse:'): seen = True
        if seen and l != '' and not l.startswith('CallStack') and not l.startswith('HasCallStack'): out.append(l)
    return out
def run(i):
    w = f'/tmp/bx/ealm1/w{i % 8}'
    os.makedirs(w, exist_ok=True)
    if not os.path.exists(w + '/Prelude.tel'): os.symlink('/tmp/bx/master98d/Prelude.tel', w + '/Prelude.tel')
    d = f'{w}/{i}'
    os.makedirs(d, exist_ok=True)
    if not os.path.exists(d + '/Prelude.tel'): os.symlink('/tmp/bx/master98d/Prelude.tel', d + '/Prelude.tel')
    open(d + '/p1.rs', 'w').write(progs[i])
    try:
        r = subprocess.run([binp], cwd=d, capture_output=True, text=True, timeout=300)
        out = r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        out = 'TIMEOUT'
    return i, out
res = {}
with cf.ThreadPoolExecutor(8) as ex:
    for i, out in ex.map(run, range(len(progs))):
        res[i] = out
same = diff = crash = 0
with open(os.environ.get('PARLOG', 'par.log'), 'w') as f:
    for i in range(len(progs)):
        mine = norm(res[i].split('\n'))
        theirs = norm(blocks[i]) if i < len(blocks) else ['?']
        tag = 'same' if mine == theirs else ('crash' if not mine else 'DIFF')
        if tag == 'same': same += 1
        elif tag == 'crash': crash += 1
        else: diff += 1
        f.write(f'{i:4} {tag:5} {progs[i][:70]!r}\n')
        if tag != 'same':
            f.write('   mine  : ' + repr(mine[:2] if mine else res[i].strip()[:300])[:600] + '\n')
            f.write('   master: ' + repr(theirs[:2])[:600] + '\n')
    f.write(f'same {same} diff {diff} crash {crash}\n')
print('same', same, 'diff', diff, 'crash', crash)
