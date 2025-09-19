-- <vc-preamble>
def Matrix (α : Type u) (n : Nat) := Array (Array α)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def standardDeterminant {n : Nat} (M : Matrix Int n) : Int :=
sorry

def identityMatrix (n : Nat) : Matrix Int n :=
sorry

def zeroMatrix (n : Nat) : Matrix Int n :=
sorry

def scaleMatrix {n : Nat} (c : Int) (M : Matrix Int n) : Matrix Int n :=
sorry

def determinant {n : Nat} (M : Matrix Int n) : Int :=
sorry
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
-- </vc-theorems>