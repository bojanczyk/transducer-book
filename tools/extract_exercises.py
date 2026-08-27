import re, sys, os

FILES = ["intro","mealy","krohn-rhodes","rational-relations","rational-functions",
         "weighted","myhill-nerode","regular-intro","regular-primes","2dfa","sst",
         "logic","polyregular-intro","polyregular-for","polyregular-pebble"]

ROOT = os.path.join(os.path.dirname(__file__), "..", "..")

def match_brace(s, i):
    # s[i] == '{'
    assert s[i] == '{'
    d = 0
    j = i
    while j < len(s):
        if s[j] == '\\':
            j += 2
            continue
        if s[j] == '{': d += 1
        elif s[j] == '}':
            d -= 1
            if d == 0: return j
        j += 1
    raise ValueError("unbalanced")

out = []
for f in FILES:
    path = os.path.join(ROOT, f + ".tex")
    s = open(path).read()
    for m in re.finditer(r'\\exer\s*\{', s):
        i = m.end() - 1
        j = match_brace(s, i)
        stmt = s[i+1:j]
        k = j+1
        while k < len(s) and s[k] in ' \n\t%': 
            if s[k]=='%':
                while k < len(s) and s[k] != '\n': k+=1
            k += 1
        if k >= len(s) or s[k] != '{':
            sol = None
        else:
            l = match_brace(s, k)
            sol = s[k+1:l]
        lab = re.search(r'\\label\{([^}]*)\}', stmt)
        out.append((f, s[:i].count('\n')+1, lab.group(1) if lab else None,
                    len(sol.strip()) if sol is not None else -1, stmt, sol))

for idx,(f,line,lab,sl,stmt,sol) in enumerate(out):
    print(f"{idx:3d} {f:22s} L{line:5d} sol={sl:5d} {lab}")
print("total", len(out), "with sol", sum(1 for x in out if x[3]>0))

if len(sys.argv) > 1:
    with open(sys.argv[1], "w") as fh:
        for idx,(f,line,lab,sl,stmt,sol) in enumerate(out):
            fh.write(f"\n\n===== [{idx}] {f} line {line} label={lab} =====\nSTATEMENT:\n{stmt}\nSOLUTION:\n{sol}\n")
