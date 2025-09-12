/-
  Port of Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_mathematical objects verification_examples_fast_exp_FastExp.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def sum (s : seq<int>) (i : Nat) : Int :=
  sorry  -- TODO: implement complex function body

def exp (b : Nat) (n : Nat) : Nat :=
  sorry  -- TODO: implement function body

def bits (n : Nat) : seq :=
  sorry  -- TODO: implement function body

def from_bits (s : seq<bool>) : Nat :=
  sorry  -- TODO: implement function body

def FastExp (b : Nat) (n : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem FastExp_spec (b : Nat) (n : Nat) (r : Nat) :=
  : r == exp(b, n)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks