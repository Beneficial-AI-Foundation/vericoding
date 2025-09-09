-- <vc-helpers>
-- </vc-helpers>

def minFlipsMonoIncr (s : String) : Nat :=
  sorry

theorem result_length_within_bounds (s : String) : 
  let result := minFlipsMonoIncr s
  0 ≤ result ∧ result ≤ s.length :=
  sorry

theorem edge_cases :
  minFlipsMonoIncr "" = 0 ∧ 
  (∀ n : Nat, minFlipsMonoIncr (String.mk (List.replicate n '0')) = 0) ∧
  (∀ n : Nat, minFlipsMonoIncr (String.mk (List.replicate n '1')) = 0) :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval minFlipsMonoIncr "00110"

/-
info: 2
-/
-- #guard_msgs in
-- #eval minFlipsMonoIncr "010110"

/-
info: 2
-/
-- #guard_msgs in
-- #eval minFlipsMonoIncr "00011000"

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible