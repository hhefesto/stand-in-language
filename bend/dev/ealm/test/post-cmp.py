import sys,re
def norm(path):
    head=[];gs=[]
    for l in open(path):
        l=l.rstrip('\n')
        if l.startswith('g '):
            l=re.sub(r' h [0-9a-f]+$','',l)
            l=re.sub(r"FunctionIndex {unFunctionIndex = (-?\d+)}",r"\1",l)
            m=re.match(r'g (-?\d+) (.*) usage (.*)$',l)
            fi=int(m.group(1)); us=','.join(sorted(m.group(3).split(','))) if m.group(3) else ''
            gs.append((fi,m.group(2)+' usage '+us))
        else: head.append(l)
    return head, sorted(gs)
a=norm(sys.argv[1]); b=norm(sys.argv[2])
ok=True
if a[0]!=b[0]:
    ok=False; print('HEAD port:',a[0]); print('HEAD mast:',b[0])
from collections import Counter
ca=Counter(a[1]); cb=Counter(b[1])
for k in sorted(set(ca)|set(cb)):
    if ca[k]!=cb[k]:
        ok=False; print('port %d master %d: g %d %s'%(ca[k],cb[k],k[0],k[1][:200]))
print('SAME' if ok else 'DIFF', len(a[1]), len(b[1]))
