import sys
cps = [c for c in range(0x80, 0x110000) if not (0xD800 <= c <= 0xDFFF)]
open("cps.txt", "w").write("\n".join(map(str, cps)))
L = [chr(c) for c in cps]
open("letter.cases", "w", encoding="utf-8").write("\x1e".join(L))
open("alnum.cases", "w", encoding="utf-8").write("\x1e".join("a" + x for x in L))
open("space.cases", "w", encoding="utf-8").write("\x1e".join("if" + x + "1 then 1 else 1" for x in L))
open("wide.cases", "w", encoding="utf-8").write("\x1e".join('x = "' + x + '" (' for x in L))
print(len(cps))
