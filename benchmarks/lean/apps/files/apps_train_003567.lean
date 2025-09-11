-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def round_to_five (numbers : List Float) : List Float := sorry

theorem round_to_five_multiple_of_five (numbers : List Float) :
  let result := round_to_five numbers
  ∀ x ∈ result, ∃ n : Float, x = n * 5 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem round_to_five_close_to_original (numbers : List Float) :
  let result := round_to_five numbers
  ∀ (orig rounded : Float), 
    orig ∈ numbers → rounded ∈ result →
    Float.abs (orig - rounded) ≤ 2.5 := sorry

theorem round_to_five_preserves_length (numbers : List Float) :
  List.length (round_to_five numbers) = List.length numbers := sorry

theorem round_to_five_empty :
  round_to_five [] = [] := sorry

theorem round_to_five_exact_multiples (n : Float) :
  round_to_five [n * 5] = [n * 5] := sorry

/-
info: [0, 5, 85, 45, 10, 10]
-/
-- #guard_msgs in
-- #eval round_to_five [1, 5, 87, 45, 8, 8]

/-
info: [5, 55, 10, 15]
-/
-- #guard_msgs in
-- #eval round_to_five [3, 56.2, 11, 13]

/-
info: [25, 545, 80]
-/
-- #guard_msgs in
-- #eval round_to_five [22.5, 544.9, 77.5]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded