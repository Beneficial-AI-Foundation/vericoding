/-
  Port of CVS-Projto1_tmp_tmpb1o0bu8z_Hoare_MaxA.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def fib (n : Nat) : Nat :=
  sorry  -- TODO: implement complex function body

def add (l : List<int>) : Int :=
  match l case Nil => 0 case Cons(x, xs) => x + add(xs)

def MaxA (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem MaxA_spec (a : Array Int) (m : Int) :=
  (h_0 : a.size > 0)
  : ∀ i :: 0 ≤ i < a.size → a[i]! ≤ m ∧ ∃ i, 0 ≤ i < a.size ∧ a[i]! == m
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks