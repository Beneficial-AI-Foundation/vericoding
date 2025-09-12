/-
  Port of nitwit_tmp_tmplm098gxz_nit_nit_add_three.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def sum (s : seq<int>) (i : Nat) : Int :=
  sorry  -- TODO: implement complex function body

def nit_add (b : Nat) (x : Nat) (y : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem nit_add_spec (b : Nat) (x : Nat) (y : Nat) (z : Nat) :=
  (h_0 : (valid_base(b)))
  (h_1 : (nitness(b, x)))
  (h_2 : (nitness(b, y)))
  :  (nitness(b, z)) ∧  (nitness(b, carry))
  := by
  sorry  -- TODO: implement proof

def nit_add_three (b : Nat) (c : Nat) (x : Nat) (y : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem nit_add_three_spec (b : Nat) (c : Nat) (x : Nat) (y : Nat) (z : Nat) :=
  (h_0 : (valid_base(b)))
  (h_1 : (c == 0 ∨ c == 1))
  (h_2 : (nitness(b, x)))
  (h_3 : (nitness(b, y)))
  :  (nitness(b, z)) ∧  (nitness(b, carry)) ∧  (carry == 0 ∨ carry == 1)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks