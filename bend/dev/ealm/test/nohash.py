import sys, subprocess, os, re, concurrent.futures as cf
progs = [l.replace('\\n', '\n') for l in open('corpus.txt').read().split('\n') if l]
blocks = []
for of in sys.argv[2:]:
    cur = None
    for line in open(of).read().split('\n'):
        if line.startswith('== '):
            if cur is not None: blocks.append(cur)
            cur = [line]
        elif cur is not None: cur.append(line)
    if cur is not None: blocks.append(cur)
bad = [int(l.split()[0]) for l in open(sys.argv[1]) if re.match(r'^ *\d+ (DIFF|crash)', l)]
def norm(ls):
    out = []
    for l in ls:
        if not l or l.startswith('== ') or l.startswith('CallStack') or l.startswith('HasCallStack') or l.startswith('  collect') or l.startswith('  toExc') or l.startswith('  error,'): continue
        m = re.match(r'^  ([0-9a-f]{8}) (.*)$', l)
        if m: out.append(('1', m.group(2)))
        else: out.append(('0', l))
    return sorted(out)
def run(i):
    d = f'/tmp/bx/ealm1/w{i % 8}/{i}'
    r = subprocess.run([os.environ.get('BIN', '/tmp/bx/eal2/t/m1b.bin')], cwd=d, capture_output=True, text=True)
    return i, r.stdout
real = []
hashonly = 0
with cf.ThreadPoolExecutor(8) as ex:
    for i, out in ex.map(run, bad):
        a = norm(blocks[i]); b = norm(out.split('\n'))
        if a == b: hashonly += 1
        else: real.append(i)
print('hash-only', hashonly, 'real', len(real))
open(os.environ.get('REAL', 'real.txt'), 'w').write('\n'.join(map(str, real)) + '\n')
