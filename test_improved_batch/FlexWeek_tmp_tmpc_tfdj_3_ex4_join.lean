/-
  Port of FlexWeek_tmp_tmpc_tfdj_3_ex4_join.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def join (a : Array Int) (b : Array Int) : Array Int :=
  sorry  -- TODO: implement function body

theorem join_spec (a : Array Int) (b : Array Int) (c : Array Int) :=
  : a[..] + b[..] == c[..] ∧ multiset(a[..] + b[..]) == multiset(c[..]) ∧ multiset(a[..]) + multiset(b[..]) == multiset(c[..]) ∧ a.size+b.size == c.size
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks