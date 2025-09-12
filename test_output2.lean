/-
  Port of 630-dafny_tmp_tmpz2kokaiq_Solution_BinarySearch.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def sorted (a : Array Int) : Bool :=
  sorry  -- TODO: implement function body

def BinarySearch (a : Array Int) (x : Int) : (index : Int) :=
  (h_0 : sorted(a))
  : 0 ≤ index < a.size → a[index]! == x ∧ index == -1 → ∀ i : int :: 0 ≤ i < a.size → a[i]! ≠ x
  sorry  -- TODO: implement method body

end DafnyBenchmarks