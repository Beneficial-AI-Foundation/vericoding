/-
  Port of vericoding_dafnybench_0377_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def max (a : Int) (b : Int) : Int :=
  sorry  -- TODO: implement function body

theorem max_spec (a : Int) (b : Int) (z : Int) :=
  (h_0 : true)
  : z ≥ a ∨ z ≥ b
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

def mystery1 (n : Nat) (m : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem mystery1_spec (n : Nat) (m : Nat) (res : Nat) :=
  : n+m == res
  := by
  sorry  -- TODO: implement proof

def mystery2 (n : Nat) (m : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem mystery2_spec (n : Nat) (m : Nat) (res : Nat) :=
  : n*m == res
  := by
  sorry  -- TODO: implement proof

def m1 (x : Int) (y : Int) : Int :=
  sorry  -- TODO: implement function body

theorem m1_spec (x : Int) (y : Int) (z : Int) :=
  (h_0 : 0 < x < y)
  : z ≥ 0 ∧ z < y ∧ z ≠ x
  := by
  sorry  -- TODO: implement proof

def m2 (x : Nat) : Int :=
  sorry  -- TODO: implement function body

theorem m2_spec (x : Nat) (y : Int) :=
  (h_0 : x ≤ -1)
  : y > x ∧ y < x
  := by
  sorry  -- TODO: implement proof

def m3 (x : Int) (y : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem m3_spec (x : Int) (y : Int) (z : Bool) :=
  : z → x==y
  := by
  sorry  -- TODO: implement proof

def m4 (x : Int) (y : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem m4_spec (x : Int) (y : Int) (z : Bool) :=
  : z → x==y ∧ x==y → z
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks