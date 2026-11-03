import sys, re
# reads oracle output; prints index and first line of each case's output
idx = None; want = False
out = sys.stdout
for line in sys.stdin:
    m = re.match(r'^== (\d+)$', line.rstrip('\n'))
    if m and want is False:
        idx = int(m.group(1)); want = True; continue
    if m and want:
        idx = int(m.group(1)); continue
    if want:
        out.write("%d %s\n" % (idx, line.rstrip('\n')[:40])); want = False
