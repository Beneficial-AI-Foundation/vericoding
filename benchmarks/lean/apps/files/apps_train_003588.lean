-- <vc-helpers>
-- </vc-helpers>

def past (h: Nat) (m: Nat) (s: Nat) : Nat :=
  sorry

theorem past_valid_time {h m s: Nat} 
  (hh: h ≤ 23) (hm: m ≤ 59) (hs: s ≤ 59) : 
  past h m s = (h * 3600 + m * 60 + s) * 1000 
  ∧ past h m s < 24 * 60 * 60 * 1000 :=
sorry

theorem past_zero_seconds {h m: Nat}
  (hh: h ≤ 23) (hm: m ≤ 59) :
  past h m 0 = (h * 3600 + m * 60) * 1000 :=
sorry 

theorem past_midnight :
  past 0 0 0 = 0 :=
sorry

/-
info: 61000
-/
-- #guard_msgs in
-- #eval past 0 1 1

/-
info: 3661000
-/
-- #guard_msgs in
-- #eval past 1 1 1

/-
info: 0
-/
-- #guard_msgs in
-- #eval past 0 0 0

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible