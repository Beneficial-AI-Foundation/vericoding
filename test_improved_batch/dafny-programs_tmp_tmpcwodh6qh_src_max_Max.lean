/-
  Port of dafny-programs_tmp_tmpcwodh6qh_src_max_Max.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def max (a : Int) (b : Int) : Int :=
  if a > b then a else b

def Max (a : Int) (b : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Max_spec (a : Int) (b : Int) (c : Int) :=
  : a ≥ b → c == a ∧ b ≥ a → c == b
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks