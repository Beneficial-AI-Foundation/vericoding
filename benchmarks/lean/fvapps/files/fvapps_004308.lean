-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def distance (x y : Float) : Float :=
  sorry

def angle (x y : Float) : Float :=
  sorry

def get_score (x y : Float) : String :=
  sorry

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
-- </vc-theorems>