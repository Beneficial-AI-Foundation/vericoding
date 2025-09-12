/-
  Port of vericoding_dafnybench_0378_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def fib (n : Nat) : Nat :=
  sorry  -- TODO: implement complex function body

def add (l : List<int>) : Int :=
  sorry  -- TODO: implement function body

def sum (n : Nat) : Nat :=
  sorry  -- TODO: implement complex function body

def Fib (n : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem Fib_spec (n : Nat) (r : Nat) :=
  : r == fib(n)
  := by
  sorry  -- TODO: implement proof

def addImp (l : List<int>) : Int :=
  sorry  -- TODO: implement function body

theorem addImp_spec (l : List<int>) (r : Int) :=
  : r == add(l)
  := by
  sorry  -- TODO: implement proof

def maxArray (arr : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem maxArray_spec (arr : Array Int) (max : Int) :=
  (h_0 : arr.size > 0)
  : ∀ i : Int, 0 ≤ i < arr.size → arr[i]! ≤ max ∧ ∃ x, 0 ≤ x < arr.size ∧ arr[x]! == max
  := by
  sorry  -- TODO: implement proof

def maxArrayReverse (arr : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem maxArrayReverse_spec (arr : Array Int) (max : Int) :=
  (h_0 : arr.size > 0)
  : ∀ i : Int, 0 ≤ i < arr.size → arr[i]! ≤ max ∧ ∃ x, 0 ≤ x < arr.size ∧ arr[x]! == max
  := by
  sorry  -- TODO: implement proof

def sumBackwards (n : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem sumBackwards_spec (n : Nat) (r : Nat) :=
  : r == sum(n)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks