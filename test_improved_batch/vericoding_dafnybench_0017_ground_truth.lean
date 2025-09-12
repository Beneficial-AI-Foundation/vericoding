/-
  Port of vericoding_dafnybench_0017_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def fib (n : Nat) : Nat :=
  sorry  -- TODO: implement complex function body

def add (l : List<int>) : Int :=
  match l case Nil => 0 case Cons(x, xs) => x + add(xs)

def Max (x : Nat) (y : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem Max_spec (x : Nat) (y : Nat) (r : Nat) :=
  : (r ≥ x ∧ r ≥y) ∧ (r == x ∨ r == y)
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

def m1 (x : Int) (y : Int) : Int :=
  sorry  -- TODO: implement function body

theorem m1_spec (x : Int) (y : Int) (z : Int) :=
  (h_0 : 0 < x < y)
  : z ≥ 0 ∧ z ≤ y ∧ z ≠ x
  := by
  sorry  -- TODO: implement proof

def Fib (n : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem Fib_spec (n : Nat) (r : Nat) :=
  : r == fib(n)
  := by
  sorry  -- TODO: implement proof

def addImp (l : List<int>) : Int :=
  sorry  -- TODO: implement function body

theorem addImp_spec (l : List<int>) (s : Int) :=
  : s == add(l)
  := by
  sorry  -- TODO: implement proof

def MaxA (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem MaxA_spec (a : Array Int) (m : Int) :=
  (h_0 : a.size > 0)
  : ∀ i :: 0 ≤ i < a.size → a[i]! ≤ m ∧ ∃ i, 0 ≤ i < a.size ∧ a[i]! == m
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks