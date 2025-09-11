-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_it (seq: List Int) : Int := sorry

theorem find_it_exists_in_odds {seq: List Int} (h: seq ≠ []) :
  let result := find_it seq
  let odds := seq.filter (fun x => seq.count x % 2 = 1)
  odds ≠ [] → odds.contains result := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: 5
-/
-- #guard_msgs in
-- #eval find_it [20, 1, -1, 2, -2, 3, 3, 5, 5, 1, 2, 4, 20, 4, -1, -2, 5]

/-
info: -1
-/
-- #guard_msgs in
-- #eval find_it [1, 1, 2, -2, 5, 2, 4, 4, -1, -2, 5]

/-
info: 10
-/
-- #guard_msgs in
-- #eval find_it [10]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible