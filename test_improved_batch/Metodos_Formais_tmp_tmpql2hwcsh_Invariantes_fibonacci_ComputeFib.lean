/-
  Port of Metodos_Formais_tmp_tmpql2hwcsh_Invariantes_fibonacci_ComputeFib.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Fib (n : Nat) : Nat :=
  if n < 2 then n else Fib(n-2) + Fib(n-1)

def ComputeFib (n : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem ComputeFib_spec (n : Nat) (x : Nat) :=
  : x == Fib(n)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks