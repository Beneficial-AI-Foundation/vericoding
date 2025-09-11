-- <vc-preamble>
def Matrix (α : Type u) (n : Nat) := Array (Array α)

def standardDeterminant {n : Nat} (M : Matrix Int n) : Int := sorry

def identityMatrix (n : Nat) : Matrix Int n := sorry
def zeroMatrix (n : Nat) : Matrix Int n := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def scaleMatrix {n : Nat} (c : Int) (M : Matrix Int n) : Matrix Int n := sorry
def determinant {n : Nat} (M : Matrix Int n) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem determinant_matches_standard_implementation {n : Nat} (M : Matrix Int n) :
  determinant M = standardDeterminant M := 
  sorry

theorem determinant_identity {n : Nat} :
  determinant (identityMatrix n) = 1 :=
  sorry 

theorem determinant_zero {n : Nat} :
  determinant (zeroMatrix n) = 0 :=
  sorry

theorem determinant_scaling {n : Nat} (M : Matrix Int n) (c : Int) :
  determinant (scaleMatrix c M) = c^n * determinant M :=
  sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval determinant #[[5]]

/-
info: -2
-/
-- #guard_msgs in
-- #eval determinant #[[1, 2], [3, 4]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval determinant #[[1, 2, 3], [4, 5, 6], [7, 8, 9]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded