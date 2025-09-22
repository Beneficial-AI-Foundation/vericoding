-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def yoga (classroom : List (List Nat)) (poses : List Nat) : Nat := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem yoga_nonnegative (classroom : List (List Nat)) (poses : List Nat) :
  yoga classroom poses ≥ 0 := sorry

theorem yoga_empty_inputs (classroom : List (List Nat)) (poses : List Nat) :
  classroom = [] ∨ poses = [] → yoga classroom poses = 0 := sorry
-- </vc-theorems>