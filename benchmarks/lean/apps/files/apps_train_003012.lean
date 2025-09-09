-- <vc-helpers>
-- </vc-helpers>

def count_odd_pentaFib (n : Nat) : Nat :=
  sorry

theorem count_odd_pentaFib_nonnegative (n : Nat) :
  count_odd_pentaFib n ≥ 0 :=
  sorry

theorem count_odd_pentaFib_first_terms (n : Nat) (h : n ≤ 5) :
  count_odd_pentaFib n = match n with
    | 0 => 0
    | 1 => 1  
    | 2 => 1
    | 3 => 1
    | 4 => 1
    | 5 => 1
    | _ => 0
  :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_odd_pentaFib 0

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_odd_pentaFib 1

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_odd_pentaFib 2

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible