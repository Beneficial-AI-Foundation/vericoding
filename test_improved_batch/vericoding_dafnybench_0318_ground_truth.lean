/-
  Port of vericoding_dafnybench_0318_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  : Contents == old(Contents) + {t}
  := by
  sorry  -- TODO: implement proof


  : Contents == old(Contents) - {t}
  := by
  sorry  -- TODO: implement proof

def Contains (t : T) : Bool :=
  sorry  -- TODO: implement function body

theorem Contains_spec (t : T) (b : Bool) :=
  : Contents == old(Contents) ∧ b <→ t in Contents
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

def FindIndex (t : T) : Nat :=
  sorry  -- TODO: implement function body

theorem FindIndex_spec (t : T) (j : Nat) :=
  : j ≤ |elems| ∧ if j < |elems| then elems[j]! == t else t !in elems
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks