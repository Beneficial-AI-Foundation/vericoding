-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_dot (a b : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_dot_le_standard_dot (a b : List Int) :
  min_dot a b ≤ (List.zip a b).foldl (fun acc (x : Int × Int) => acc + x.1 * x.2) 0 :=
sorry

theorem min_dot_commutative (a b : List Int) :
  min_dot a b = min_dot b a :=
sorry

theorem min_dot_empty :
  min_dot ([] : List Int) ([] : List Int) = 0 :=
sorry

theorem min_dot_permutation (a b : List Int) (perm_a : List Int) (perm_b : List Int)
    (h1 : List.Perm a perm_a) (h2 : List.Perm b perm_b) :
  min_dot perm_a perm_b = min_dot a b :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_dot [] []

/-
info: 6
-/
-- #guard_msgs in
-- #eval min_dot [1, 2, 3, 4, 5] [0, 1, 1, 1, 0]

/-
info: -17
-/
-- #guard_msgs in
-- #eval min_dot [1, 2, 3, 4, 5] [0, 0, 1, 1, -4]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded