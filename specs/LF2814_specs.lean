-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def subcuboids (x y z : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cube_symmetry (n : Nat) (h : n > 0) : 
  subcuboids n n n = subcuboids n n n :=
by sorry

theorem dimensions_positive (x y z : Nat) (hx : x > 0) (hy : y > 0) (hz : z > 0) :
  subcuboids x y z > 0 :=
by sorry

theorem dimension_symmetry (x y z : Nat) (hx : x > 0) (hy : y > 0) (hz : z > 0) :
  subcuboids x y z = subcuboids x z y ∧ 
  subcuboids x y z = subcuboids y x z ∧
  subcuboids x y z = subcuboids y z x ∧ 
  subcuboids x y z = subcuboids z x y ∧
  subcuboids x y z = subcuboids z y x :=
by sorry
-- </vc-theorems>