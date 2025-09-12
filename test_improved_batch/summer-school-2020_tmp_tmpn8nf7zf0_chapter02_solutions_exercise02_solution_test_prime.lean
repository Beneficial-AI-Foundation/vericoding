/-
  Port of summer-school-2020_tmp_tmpn8nf7zf0_chapter02_solutions_exercise02_solution_test_prime.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def test_prime (i : Nat) : Bool :=
  sorry  -- TODO: implement function body

theorem test_prime_spec (i : Nat) (result : Bool) :=
  (h_0 : 1<i)
  : result == IsPrime(i)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks