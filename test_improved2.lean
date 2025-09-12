/-
  Port of 630-dafny_tmp_tmpz2kokaiq_Solution_BinarySearch.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def sorted (a : Array Int) : Bool :=
  sorry  -- TODO: implement function body

def BinarySearch (a : Array Int) (x : Int) : Int :=
  sorry  -- TODO: implement function body

theorem BinarySearch_spec (a : Array Int) (x : Int) :=
  (h_0 : sorted(a))
  : 0 ≤ index < a.size → a[index]! == x ∧ index == -1 → ∀ i : Int :: 0 ≤ i < a.size → a[i]! ≠ x
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks