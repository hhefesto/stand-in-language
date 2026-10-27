// nt.reduce (bend/Native.bend) on the JavaScript target: no native loop
// here, so it fires nothing and hands every pair back to Bend, which fires
// it with IC.bend's own code. The C side (ic.c) is the fast one.
function nt_reduce(mem, tpl, sp, bump, free, label, fuel, err, cap) {
  return io_tup(mem, tpl, sp, bump, free, label, fuel, err, cap, 0);
}

io_eff(CID(nt.reduce), nt_reduce);
