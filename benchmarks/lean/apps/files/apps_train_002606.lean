-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cube_odd (xs : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cube_odd_integers (xs : List Int) :
  cube_odd xs = (xs.filter (fun x => x % 2 ≠ 0)
                |>.map (fun x => x * x * x)
                |>.foldl (· + ·) 0 : Int)
  := sorry

theorem cube_odd_bounded (xs : List Int) 
  (h : ∀ x ∈ xs, -1000 ≤ x ∧ x ≤ 1000) :
  cube_odd xs = (xs.filter (fun x => x % 2 ≠ 0)
                |>.map (fun x => x * x * x)
                |>.foldl (· + ·) 0 : Int)
  := sorry

theorem cube_odd_non_empty (xs : List Int)
  (h : xs ≠ []) : 
  cube_odd xs = (xs.filter (fun x => x % 2 ≠ 0)
                |>.map (fun x => x * x * x)
                |>.foldl (· + ·) 0 : Int)
  := sorry

/-
info: 28
-/
-- #guard_msgs in
-- #eval cube_odd [1, 2, 3, 4]

/-
info: 0
-/
-- #guard_msgs in
-- #eval cube_odd [-3, -2, 2, 3]

/-
info: None
-/
-- #guard_msgs in
-- #eval cube_odd ["a", 12, 9, "z", 42]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded