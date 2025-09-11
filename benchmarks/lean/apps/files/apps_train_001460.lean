-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MOD := 1000000007

def calculate_wonder_sum (strings : List String) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calculate_wonder_sum_length (strings : List String) :
  strings ≠ [] →
  List.length (calculate_wonder_sum strings) = List.length strings :=
  sorry

/-
info: [903, 7630]
-/
-- #guard_msgs in
-- #eval calculate_wonder_sum ["cab", "sdef"]

/-
info: [100]
-/
-- #guard_msgs in
-- #eval calculate_wonder_sum ["a"]

/-
info: [2625]
-/
-- #guard_msgs in
-- #eval calculate_wonder_sum ["z"]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible