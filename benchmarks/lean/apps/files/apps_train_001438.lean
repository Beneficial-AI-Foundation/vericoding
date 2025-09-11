-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_kills_needed (n : Nat) (heights : List Nat) : Nat := sorry

theorem result_bounds {n : Nat} {heights : List Nat} (h1 : heights.length = n) (h2 : n > 0) :
  let result := min_kills_needed n heights
  result ≤ n ∧ result ≥ (n + 1) / 2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem same_height {n : Nat} {heights : List Nat} {h : Nat}
  (h1 : heights = List.replicate n h) (h2 : n > 0) :
  min_kills_needed n heights = n := sorry

theorem alternating_heights {n : Nat} {h : Nat} (h1 : n > 0) :
  let heights := List.replicate (n/2) h ++ List.replicate (n/2) (h+1) ++
                 (if n % 2 = 1 then [h] else [])
  min_kills_needed n heights = (n + 1) / 2 := sorry

theorem mode_dominance {n : Nat} {heights : List Nat} (h1 : heights.length = n) (h2 : n > 0)
  (h3 : ∃ x : Nat, (List.count x heights) * 2 > n) :
  min_kills_needed n heights = List.count (Classical.choose h3) heights := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval min_kills_needed 10 [178, 184, 178, 177, 171, 173, 171, 183, 171, 175]

/-
info: 5
-/
-- #guard_msgs in
-- #eval min_kills_needed 5 [100, 100, 100, 100, 100]

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_kills_needed 4 [101, 102, 103, 104]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded