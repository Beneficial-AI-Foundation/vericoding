-- <vc-preamble>
def isInertial (arr : List Int) : Bool := sorry

def maximum? : List Int → Option Int
  | [] => none
  | x::xs => some (xs.foldl max x)
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minimum? : List Int → Option Int
  | [] => none
  | x::xs => some (xs.foldl min x)
-- </vc-definitions>

-- <vc-theorems>
theorem empty_array
  : ∀ (arr : List Int), arr = [] → isInertial arr = false := by
  sorry

theorem no_odds
  : ∀ (arr : List Int),
    arr ≠ [] →
    (∀ x ∈ arr, x % 2 = 0) →
    isInertial arr = false := by
  sorry

theorem max_must_be_even
  : ∀ (arr : List Int),
    arr ≠ [] →
    match maximum? arr with
    | none => True
    | some max => max % 2 = 1 → isInertial arr = false := by
  sorry

theorem odds_vs_evens
  : ∀ (arr : List Int),
    arr ≠ [] →
    (∃ x ∈ arr, x % 2 = 1) →
    match maximum? arr with
    | none => True
    | some max =>
      max % 2 = 0 →
      let odds := arr.filter (fun x => x % 2 = 1)
      let evens := arr.filter (fun x => x % 2 = 0 && x ≠ max)
      odds ≠ [] →
      evens ≠ [] →
      match minimum? odds, maximum? evens with
      | some min_odd, some max_even => isInertial arr = (min_odd > max_even)
      | _, _ => True := by
  sorry

theorem single_element
  : ∀ (n : Int), isInertial [n] = false := by
  sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval is_inertial []

/-
info: False
-/
-- #guard_msgs in
-- #eval is_inertial [581, -384, 140, -287]

/-
info: True
-/
-- #guard_msgs in
-- #eval is_inertial [11, 4, 20, 9, 2, 8]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded