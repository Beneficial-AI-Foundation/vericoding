/-
  Port of vericoding_dafnybench_0672_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

function {:opaque} DivSub(a: int, b: int): int
  if a < b then 0 else 1 + DivSub(a - b, b)

function {:opaque} ModSub(a: int, b: int): int
  if a < b then a else ModSub(a - b, b)

end DafnyBenchmarks