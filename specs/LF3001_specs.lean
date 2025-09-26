-- <vc-preamble>
def List.sum : List Int → Int
| [] => 0
| (x :: xs) => x + sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def number (stops : List (Int × Int)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bus_stops_non_negative (stops : List (Int × Int)) 
  (h : ∀ s ∈ stops, s.1 ≥ 0 ∧ s.2 ≥ 0 ∧ s.1 ≥ s.2) : 
  number stops ≥ 0 :=
  sorry

theorem zero_passengers (stops : List (Int × Int))
  (h : ∀ s ∈ stops, s.1 = 0 ∧ s.2 = 0) :
  number stops = 0 :=
  sorry

theorem sum_equals_difference (stops : List (Int × Int))
  (h : ∀ s ∈ stops, s.1 ≥ 0 ∧ s.2 ≥ 0 ∧ s.1 ≥ s.2) :
  number stops = List.sum (stops.map (fun s => s.1 - s.2)) :=
  sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval number [[10, 0], [3, 5], [5, 8]]

/-
info: 17
-/
-- #guard_msgs in
-- #eval number [[3, 0], [9, 1], [4, 10], [12, 2], [6, 1], [7, 10]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval number [[0, 0]]
-- </vc-theorems>