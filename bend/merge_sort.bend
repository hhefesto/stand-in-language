# Merge-sort sorting network in Bend (Higher Order Co's auto-parallel language,
# HVM2 runtime) — a hand port of telomare's `mergeSortS`.
#
# This is the "execution substrate" half of the symbiosis: telomare proves the
# network sorts AND its cost (work 38 / span 6 for the 8-wire version, via the
# (work, span) functor in telomare.agda); HVM *runs* it, reducing the independent
# compare-and-swaps within each layer in parallel — no thread/lock annotations.

# Compare-and-swap: (min, max).  This IS telomare's  casS = forkS minS maxS.
def cas(a, b):
  switch (a < b):
    case 0:
      return (b, a)   # a >= b
    case _:
      return (a, b)   # a <  b

# 4-input merge-sort network: sort the two pairs (0,1),(2,3), then merge with
# (0,2),(1,3),(1,2).  Same construction as telomare's mergeSortS (the 4-wire case
# that ConCat renders to out/merge-sort.svg).  Comparators within a layer are
# independent, so HVM reduces them in parallel.
def merge_sort4(a, b, c, d):
  (a, b) = cas(a, b)        # layer 1  ─┐ independent
  (c, d) = cas(c, d)        #          ─┘
  (a, c) = cas(a, c)        # layer 2  ─┐ independent
  (b, d) = cas(b, d)        #          ─┘
  (b, c) = cas(b, c)        # layer 3
  return (a, b, c, d)

def main():
  # [3,1,4,2] ↦ [1,2,3,4]
  return merge_sort4(3, 1, 4, 2)
