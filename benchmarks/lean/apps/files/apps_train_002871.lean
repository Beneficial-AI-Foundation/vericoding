-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def strCount (s : String) (letter : Char) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem strCount_nonnegative (s : String) (letter : Char) :
  strCount s letter ≥ 0 :=
sorry

theorem strCount_upper_bound (s : String) (letter : Char) :
  strCount s letter ≤ s.length :=
sorry

theorem strCount_matches_actual (s : String) (letter : Char) :
  strCount s letter = (s.data.filter (· = letter)).length :=
sorry

theorem strCount_empty (letter : Char) :
  strCount "" letter = 0 :=
sorry

theorem strCount_all_same (s : String) (letter : Char) :
  s.length > 0 → (∀ c ∈ s.data, c = letter) → strCount s letter = s.length :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval str_count "hello" "l"

/-
info: 5
-/
-- #guard_msgs in
-- #eval str_count "ggggg" "g"

/-
info: 2
-/
-- #guard_msgs in
-- #eval str_count "hello world" "o"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded