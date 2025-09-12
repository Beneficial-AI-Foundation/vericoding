/-
  Port of vericoding_dafnybench_0039_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def copy (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) : Array Int :=
  sorry  -- TODO: implement function body

theorem copy_spec (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) (r : Array Int) :=
  (h_0 : src.size ≥ sStart + len)
  (h_1 : dest.size ≥ dStart + len)
  : r.size == dest.size ∧ r[..dStart] == dest[..dStart] ∧ r[dStart + len..] == dest[dStart + len..] ∧ r[dStart..len+dStart] == src[sStart..len+sStart]
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks