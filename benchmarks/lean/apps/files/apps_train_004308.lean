-- <vc-preamble>
def distance (x y : Float) : Float := 
  sorry

def angle (x y : Float) : Float := 
  sorry

def get_score (x y : Float) : String :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ValidScores : List String := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_score_returns_valid : ∀ x y : Float, x ≥ -200 ∧ x ≤ 200 ∧ y ≥ -200 ∧ y ≤ 200 → 
  get_score x y ∈ ValidScores :=
sorry

theorem same_distance_angle_same_score : ∀ x y x2 y2 : Float,
  x ≥ -200 ∧ x ≤ 200 ∧ y ≥ -200 ∧ y ≤ 200 ∧
  x2 ≥ -200 ∧ x2 ≤ 200 ∧ y2 ≥ -200 ∧ y2 ≤ 200 →
  distance x y = distance x2 y2 ∧ angle x y = angle x2 y2 →
  get_score x y = get_score x2 y2 :=
sorry

theorem outside_board_is_X : ∀ x y : Float,
  x > 170.1 ∧ x ≤ 200 ∧ y ≥ -200 ∧ y ≤ 200 →
  get_score x y = "X" :=
sorry

theorem bulls_eye_region : ∀ x y : Float,
  x ≥ -6.35 ∧ x ≤ 6.35 ∧ y ≥ -6.35 ∧ y ≤ 6.35 ∧
  distance x y ≤ 6.35 →
  get_score x y = "DB" :=
sorry

/-
info: 'X'
-/
-- #guard_msgs in
-- #eval get_score -133.69 -147.38

/-
info: 'DB'
-/
-- #guard_msgs in
-- #eval get_score 4.06 0.71

/-
info: 'T2'
-/
-- #guard_msgs in
-- #eval get_score 55.53 -87.95
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded