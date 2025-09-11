-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def simulate_farm_program (n: Nat) (arr: List Nat) : List Int := sorry

-- Output length equals input length
-- </vc-definitions>

-- <vc-theorems>
theorem output_length_equals_input {n: Nat} {arr: List Nat} 
  (h₁: n ≥ 2)
  (h₂: arr.length = n - 1) :
  (simulate_farm_program n arr).length = n - 1 := sorry

-- Output values are either -1 or positive

theorem output_values_valid {n: Nat} {arr: List Nat} 
  (h₁: n ≥ 2)
  (h₂: arr.length = n - 1)
  (h₃: ∀ x ∈ arr, x ≥ 1) :
  ∀ x ∈ (simulate_farm_program n arr), x = -1 ∨ x > 0 := sorry

-- All ones input gives all negative ones output

theorem all_ones_gives_all_negative_ones {n: Nat} {arr: List Nat}
  (h₁: n ≥ 2)
  (h₂: arr.length = n - 1)
  (h₃: ∀ x ∈ arr, x = 1) :
  ∀ x ∈ (simulate_farm_program n arr), x = -1 := sorry

/-
info: [3, 6, 8]
-/
-- #guard_msgs in
-- #eval simulate_farm_program 4 [2, 4, 1]

/-
info: [-1, -1]
-/
-- #guard_msgs in
-- #eval simulate_farm_program 3 [1, 2]

/-
info: [3, -1, -1, -1]
-/
-- #guard_msgs in
-- #eval simulate_farm_program 5 [2, 2, 1, 3]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded