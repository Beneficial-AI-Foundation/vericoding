/-
  Port of vericoding_dafnybench_0357_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Getmini (a : Array Int) : Nat :=
  sorry  -- TODO: implement function body

theorem Getmini_spec (a : Array Int) (mini : Nat) :=
  (h_0 : a.size > 0)
  : 0 ≤ mini < a.size // mini is an index of a ∧ ∀ x :: 0 ≤ x < a.size → a[mini]! ≤ a[x]! // a[mini]! is the minimum value ∧ ∀ x :: 0 ≤ x < mini → a[mini]! < a[x]! // a[mini]! is the first min
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks