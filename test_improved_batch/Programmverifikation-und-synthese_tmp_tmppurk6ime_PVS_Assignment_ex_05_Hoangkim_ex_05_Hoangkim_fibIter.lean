/-
  Port of Programmverifikation-und-synthese_tmp_tmppurk6ime_PVS_Assignment_ex_05_Hoangkim_ex_05_Hoangkim_fibIter.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def fib (n : Nat) : Nat :=
  if n < 2 then n else fib(n-2)+fib(n-1)

def fact (n : Nat) : Nat :=
  sorry  -- TODO: implement complex function body

def fibIter (n : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem fibIter_spec (n : Nat) (a : Nat) :=
  (h_0 : n > 0)
  : a == fib(n)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks