-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_min_k_infinite_path (n: Nat) (perm: List Nat) (colors: List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_k_is_valid (n: Nat) (perm: List Nat) (colors: List Nat)
    (h1: n > 0) (h2: colors.length > 0) (h3: perm.length = colors.length) :
  let k := find_min_k_infinite_path n perm colors
  k > 0 :=
sorry

theorem min_k_divides_cycle_len (n: Nat) (colors: List Nat) 
    (h1: n > 0) (h2: colors.length > 0) (h3: colors.length = n) :
  let perm := (List.range (n-1)).map (λ x => x + 2) ++ [1]
  let k := find_min_k_infinite_path n perm colors
  k ≤ n ∧ n % k = 0 :=
sorry

theorem same_color_gives_k_one (n: Nat) (colors: List Nat) (c: Nat)
    (h1: n > 0) (h2: colors.length = n) :
  let perm := (List.range (n-1)).map (λ x => x + 2) ++ [1]
  let uniform_colors := List.replicate n c
  find_min_k_infinite_path n perm uniform_colors = 1 :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_min_k_infinite_path 4 [1, 3, 4, 2] [1, 2, 2, 3]

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_min_k_infinite_path 5 [2, 3, 4, 5, 1] [1, 2, 3, 4, 5]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_min_k_infinite_path 8 [7, 4, 5, 6, 1, 8, 3, 2] [5, 3, 6, 4, 7, 5, 8, 4]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded