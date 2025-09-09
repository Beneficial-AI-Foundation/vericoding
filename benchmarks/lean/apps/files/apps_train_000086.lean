-- <vc-helpers>
-- </vc-helpers>

def count_ambiguous_pairs (m d w : Nat) : Nat := sorry

theorem count_ambiguous_pairs_nonnegative (m d w : Nat) 
    (h1: m ≥ 1) (h2: d ≥ 1) (h3: w ≥ 1) :
    count_ambiguous_pairs m d w ≥ 0 := sorry

theorem count_ambiguous_pairs_equal_inputs (n : Nat) (h: n ≥ 1) :
    count_ambiguous_pairs n n n ≤ n * (n-1) / 2 := sorry

theorem count_ambiguous_pairs_week_one (m d : Nat) (h1: m ≥ 1) (h2: d ≥ 1) :
    count_ambiguous_pairs m d 1 ≤ min m d * (min m d - 1) / 2 := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval count_ambiguous_pairs 6 7 4

/-
info: 9
-/
-- #guard_msgs in
-- #eval count_ambiguous_pairs 10 7 12

/-
info: 5
-/
-- #guard_msgs in
-- #eval count_ambiguous_pairs 12 30 7

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible