/-
  Port of Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_basic examples_sumto_sol_Total.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def sum_up_to (n : Nat) : Nat :=
  sorry  -- TODO: implement complex function body

def total (a : seq<nat>) : Nat :=
  sorry  -- TODO: implement complex function body

def Total (a : seq<nat>) : Nat :=
  sorry  -- TODO: implement function body

theorem Total_spec (a : seq<nat>) (r : Nat) :=
  : r == total (a[0..|a|]);
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks