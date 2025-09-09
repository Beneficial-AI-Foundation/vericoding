-- <vc-helpers>
-- </vc-helpers>

def count_odds (low high : Int) : Nat :=
  sorry

theorem count_odds_correct (low high : Int) (h : high ≥ low) (h2 : high - low < 1000) :
  count_odds low high = ((List.range (Int.toNat (high - low + 1))).filter (fun n => (Int.ofNat n + low) % 2 ≠ 0)).length :=
  sorry

theorem count_odds_single_number (n : Int) :
  count_odds n n = if n % 2 = 0 then 0 else 1 :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_odds 3 7

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_odds 8 10

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_odds 0 5

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible