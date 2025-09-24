-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_drone_step (n : Nat) (R : Int) (H : List Int) : Nat :=
  sorry

variable (n : Nat) (R : Int) (H : List Int)
-- </vc-definitions>

-- <vc-theorems>
theorem max_drone_step_positive :
  n > 0 → H.length = n → max_drone_step n R H > 0 :=
  sorry

theorem max_drone_step_divides_distances : 
  n > 0 → H.length = n →
  ∀ h, h ∈ H → (h - R).natAbs % (max_drone_step n R H) = 0 :=
  sorry
-- </vc-theorems>