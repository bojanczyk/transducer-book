#!/usr/bin/env python3
"""Insert `omit ... in` before each theorem that a `lake build` log reports as
carrying automatically included section variables it does not use.

Usage: python3 tools/omit_unused.py BUILDLOG
"""
import re, sys
from collections import defaultdict

log = open(sys.argv[1]).read().split("\n")
items = []
i = 0
while i < len(log):
    m = re.match(r"warning: (RequestProject/\S+\.lean):(\d+):\d+: automatically included section variable\(s\) unused in theorem", log[i])
    if m:
        vars = []
        j = i + 1
        while j < len(log) and re.match(r"\s+\S", log[j]) and not log[j].startswith("consider"):
            vars.append(log[j].strip())
            j += 1
        items.append((m.group(1), int(m.group(2)), " ".join(vars)))
        i = j
    else:
        i += 1

byfile = defaultdict(list)
for f, l, o in items:
    byfile[f].append((l, o))

for f, lst in byfile.items():
    lines = open(f).read().split("\n")
    for l, o in sorted(set(lst), reverse=True):
        i = l - 1
        assert re.match(r"\s*(@\[|private |protected |noncomputable |theorem |lemma )", lines[i]), (f, l, lines[i])
        j = i
        if i > 0 and lines[i-1].rstrip().endswith("-/"):
            k = i - 1
            while k >= 0 and "/--" not in lines[k]:
                k -= 1
            if k >= 0:
                j = k
        indent = re.match(r"\s*", lines[i]).group(0)
        lines.insert(j, f"{indent}omit {o} in")
    open(f, "w").write("\n".join(lines))
print(f"inserted {len(set(items))} omit lines in {len(byfile)} files")
