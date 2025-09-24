-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lamps (a: List Nat) : Nat := sorry

theorem lamps_result_bounded (a: List Nat) : 
  lamps a ≤ a.length ∧ 0 ≤ lamps a := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lamps_alternating_sequence (a: List Nat) (h: a.length > 0) :
  lamps ((List.range a.length).map (fun i => i % 2)) = 0 := sorry
-- </vc-theorems>