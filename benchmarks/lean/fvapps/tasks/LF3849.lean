-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def switch_lights (input : List Nat) : List Nat := sorry

theorem switch_lights_binary_only {states : List Nat} 
  (h : ∀ x ∈ states, x = 0 ∨ x = 1) : 
  let result := switch_lights states
  (∀ x ∈ result, x = 0 ∨ x = 1) ∧ result.length = states.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem switch_lights_preserves_input {states : List Nat}
  (h : ∀ x ∈ states, x = 0 ∨ x = 1) :
  switch_lights states ≠ states := sorry

theorem switch_lights_empty :
  switch_lights [] = [] := sorry
-- </vc-theorems>