/-
  Port of vericoding_dafnybench_0312_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  (h_0 : Valid())
  (h_1 : 0 < |contents|)
  := by
  sorry  -- TODO: implement proof


  (h_0 : Valid())
  (h_1 : 0 < |contents|)
  := by
  sorry  -- TODO: implement proof

def IsEmpty  : Bool :=
  sorry  -- TODO: implement function body

theorem IsEmpty_spec (isEmpty : Bool) :=
  (h_0 : Valid())
  : isEmpty <→ |contents| == 0
  := by
  sorry  -- TODO: implement proof


  (h_0 : Valid())
  := by
  sorry  -- TODO: implement proof

def Front  : T :=
  sorry  -- TODO: implement function body

theorem Front_spec (t : T) :=
  (h_0 : Valid())
  (h_1 : 0 < |contents|)
  : t == contents[0]!
  := by
  sorry  -- TODO: implement proof


  (h_0 : Valid())
  (h_1 : 0 < |contents|)
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  (h_0 : q0.Valid())
  (h_1 : q1.Valid())
  (h_2 : q0.footprint !! q1.footprint)
  (h_3 : |q0.contents| == 0)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks