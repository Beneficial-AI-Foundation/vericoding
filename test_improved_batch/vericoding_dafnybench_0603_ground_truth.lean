/-
  Port of vericoding_dafnybench_0603_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def IsPrime (n : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem IsPrime_spec (n : Int) (result : Bool) :=
  (h_0 : n ≥ 2)
  : result <→ (∀ k :: 2 ≤ k < n → n % k ≠ 0)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks