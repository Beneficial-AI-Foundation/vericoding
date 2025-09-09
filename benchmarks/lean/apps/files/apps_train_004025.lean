-- <vc-helpers>
-- </vc-helpers>

def odd (s : String) : Nat := sorry

theorem odd_non_negative (s : String) : odd s ≥ 0 := sorry

theorem odd_smaller_than_string (s : String) : odd s ≤ s.length := sorry

theorem odd_deterministic (s : String) : odd s = odd s := sorry

theorem odd_bounded_by_chars (s : String) (h : s.data.all (fun c => c = 'o' ∨ c = 'd')) :
  odd s ≤ (s.data.filter (· = 'o')).length := sorry

theorem odd_bounded_by_d_chars (s : String) (h : s.data.all (fun c => c = 'o' ∨ c = 'd')) :
  odd s ≤ (s.data.filter (· = 'd')).length / 2 := sorry

theorem odd_empty_string : odd "" = 0 := sorry

theorem odd_no_pattern (s : String) :
  s.data.all (fun c => c = 'x') →
  odd s = 0 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval odd "oudddbo"

/-
info: 2
-/
-- #guard_msgs in
-- #eval odd "ooudddbd"

/-
info: 6
-/
-- #guard_msgs in
-- #eval odd "qoddoldfoodgodnooofostorodrnvdmddddeidfoi"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible