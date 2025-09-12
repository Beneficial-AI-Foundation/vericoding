/-
  Port of vericoding_dafnybench_0650_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def IsPerfectSquare (n : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem IsPerfectSquare_spec (n : Int) (result : Bool) :=
  (h_0 : n ≥ 0)
  : result == true → (∃ i: Int :: 0 ≤ i ≤ n ∧ i * i == n) ∧ result == false → (∀ a : Int, 0 < a*a < n → a*a ≠ n)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks