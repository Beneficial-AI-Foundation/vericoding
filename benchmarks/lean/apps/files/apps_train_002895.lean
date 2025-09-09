-- <vc-helpers>
-- </vc-helpers>

def thue_morse (n : Nat) : String := sorry

/- The length of thue_morse(n) equals n and contains only 0's and 1's -/

theorem thue_morse_length (n : Nat) : 
  (thue_morse n).length = n ∧ 
  ∀ p : String.Pos, 
    String.contains "01" ((thue_morse n).get p) := sorry

/- Any longer sequence starts with the shorter sequence -/

theorem thue_morse_prefix_consistency (n : Nat) :
  (thue_morse (n + 1)).take n = thue_morse n := sorry

/- If n > 0, the sequence starts with 0 -/

theorem thue_morse_starts_correct (n : Nat) (h : n > 0) :
  ∃ p : String.Pos, (thue_morse n).get p = '0' := sorry

/-
info: '0'
-/
-- #guard_msgs in
-- #eval thue_morse 1

/-
info: '01'
-/
-- #guard_msgs in
-- #eval thue_morse 2

/-
info: '01101'
-/
-- #guard_msgs in
-- #eval thue_morse 5

/-
info: '0110100110'
-/
-- #guard_msgs in
-- #eval thue_morse 10

-- Apps difficulty: introductory
-- Assurance level: unguarded