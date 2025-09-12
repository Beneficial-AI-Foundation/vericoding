/-
  Port of vericoding_dafnybench_0067_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def rotate (a : Array Int) (offset : Int) : Array Int :=
  sorry  -- TODO: implement function body

theorem rotate_spec (a : Array Int) (offset : Int) (b : Array Int) :=
  (h_0 : 0≤offset)
  : b.size==a.size ∧ ∀  i::0≤i<a.size →  b[i]≠=a[(i+offset)%a.size]
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks