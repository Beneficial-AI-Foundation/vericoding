/-
  Port of Software-building-and-verification-Projects_tmp_tmp5tm1srrn_CVS-projeto_aula3_maxArray.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def fib (n : Nat) : Nat :=
  sorry  -- TODO: implement complex function body

def add (l : List<int>) : Int :=
  sorry  -- TODO: implement function body

def sum (n : Nat) : Nat :=
  sorry  -- TODO: implement complex function body

def maxArray (arr : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem maxArray_spec (arr : Array Int) (max : Int) :=
  (h_0 : arr.size > 0)
  : ∀ i : Int, 0 ≤ i < arr.size → arr[i]! ≤ max ∧ ∃ x, 0 ≤ x < arr.size ∧ arr[x]! == max
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks