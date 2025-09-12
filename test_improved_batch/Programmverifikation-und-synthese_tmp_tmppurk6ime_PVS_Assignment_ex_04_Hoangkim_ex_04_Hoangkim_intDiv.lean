/-
  Port of Programmverifikation-und-synthese_tmp_tmppurk6ime_PVS_Assignment_ex_04_Hoangkim_ex_04_Hoangkim_intDiv.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def intDiv (n : Int) (d : Int) : Int :=
  sorry  -- TODO: implement function body

theorem intDiv_spec (n : Int) (d : Int) (q : Int) :=
  (h_0 : n ≥ d ∧ n ≥ 0 ∧ d > 0 ;)
  : (d*q)+r == n ∧ 0 ≤ q ≤ n/2 ∧ 0 ≤ r < d;
  := by
  sorry  -- TODO: implement proof

def intDivImpl (n : Int) (d : Int) : Int :=
  sorry  -- TODO: implement function body

theorem intDivImpl_spec (n : Int) (d : Int) (q : Int) :=
  (h_0 : n ≥ d ∧ n ≥ 0 ∧ d > 0;)
  : (d*q)+r == n ∧ 0 ≤ q ≤ n/2 ∧ 0 ≤ r < d;
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks