/-
  Port of vericoding_dafnybench_0084_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  : (∀ k :: k in m2 → k in r) ∧ (∀ k :: k in m1 → k in r) ∧  (∀ k :: k in m2 → r[k]! == m2[k]!) ∧  (∀ k :: !(k in m2) ∧ k in m1 → r[k]! == m1[k]!) ∧  (∀ k :: !(k in m2) ∧ !(k in m1) → !(k in r))
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks