/-
  Port of nitwit_tmp_tmplm098gxz_nit_nit_flip.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def sum (s : seq<int>) (i : Nat) : Int :=
  sorry  -- TODO: implement complex function body

def max_nit (b : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem max_nit_spec (b : Nat) (nmax : Nat) :=
  (h_0 : (valid_base(b)))
  : (nitness(b, nmax)) ∧ (is_max_nit(b, nmax))
  := by
  sorry  -- TODO: implement proof

def nit_flip (b : Nat) (n : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem nit_flip_spec (b : Nat) (n : Nat) (nf : Nat) :=
  (h_0 : (valid_base(b)))
  (h_1 : (nitness(b, n)))
  : (nitness (b, nf))
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks