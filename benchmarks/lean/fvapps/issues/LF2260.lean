-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | x :: xs => x + sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solveCandyBox (n : Nat) (types : List (Nat × Nat)) (flags : List Nat) : Nat × Nat := sorry

theorem all_flagged_small {n : Nat} {types : List (Nat × Nat)} {flags : List Nat}
  (h1 : n = 3)
  (h2 : types = [(1,0), (2,0), (3,0)])
  (h3 : flags = [1,1,1]) :
  let (candies, given) := solveCandyBox n types flags
  given = candies := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem none_flagged_small {n : Nat} {types : List (Nat × Nat)} {flags : List Nat}
  (h1 : n = 3)
  (h2 : types = [(1,0), (2,0), (3,0)])
  (h3 : flags = [0,0,0]) :
  let (candies, given) := solveCandyBox n types flags
  given = 0 := sorry

theorem candy_box_properties {n : Nat} {types : List (Nat × Nat)} {flags : List Nat}
  (h1 : n = types.length)
  (h2 : n = flags.length)
  (h3 : ∀ t, t ∈ types → t.1 ≥ 1 ∧ t.1 ≤ 100 ∧ t.2 = 0)
  (h4 : ∀ f, f ∈ flags → f = 0 ∨ f = 1) :
  let (candies, given) := solveCandyBox n types flags
  given ≤ candies ∧ candies ≤ n ∧ given ≤ flags.sum := sorry

/-
info: (3, 3)
-/
-- #guard_msgs in
-- #eval solve_candy_box 8 [(1, 0), (4, 1), (2, 0), (4, 1), (5, 1), (6, 1), (3, 0), (2, 0)] [0, 1, 0, 1, 1, 1, 0, 0]

/-
info: (3, 3)
-/
-- #guard_msgs in
-- #eval solve_candy_box 4 [(1, 1), (1, 1), (2, 1), (2, 1)] [1, 1, 1, 1]

/-
info: (9, 5)
-/
-- #guard_msgs in
-- #eval solve_candy_box 9 [(2, 0), (2, 0), (4, 1), (4, 1), (4, 1), (7, 0), (7, 1), (7, 0), (7, 1)] [0, 0, 1, 1, 1, 0, 1, 0, 1]
-- </vc-theorems>