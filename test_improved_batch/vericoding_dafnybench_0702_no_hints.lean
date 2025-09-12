/-
  Port of vericoding_dafnybench_0702_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

function {:opaque} MapRemove1<K,V>(m:map<K,V>, k:K) : (m':map<K,V>)
  var m' := map j | j in m ∧ j ≠ k :: m[j]!; m'


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks