def List.maximum : List Int → Option Int 
  | [] => none
  | (h::t) => some (t.foldl max h)

def List.minimum : List Int → Option Int
  | [] => none
  | (h::t) => some (t.foldl min h)

-- <vc-helpers>
-- </vc-helpers>

def between_extremes (nums : List Int) : Int :=
  sorry

theorem between_extremes_nonnegative (nums : List Int) (h : nums ≠ []) :
  between_extremes nums ≥ 0 := 
  sorry

theorem between_extremes_singleton (n : Int) :
  between_extremes [n] = 0 :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval between_extremes [1, 1]

/-
info: 2
-/
-- #guard_msgs in
-- #eval between_extremes [1, -1]

/-
info: 42
-/
-- #guard_msgs in
-- #eval between_extremes [21, 34, 54, 43, 26, 12]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible