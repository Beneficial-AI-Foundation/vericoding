-- <vc-helpers>
-- </vc-helpers>

def find_mult_3 (n : Nat) : List Nat := sorry

theorem find_mult_3_correct_for_362 :
  find_mult_3 362 = [4, 63] := sorry

theorem find_mult_3_correct_for_6063 :
  find_mult_3 6063 = [25, 6630] := sorry

theorem find_mult_3_correct_for_7766553322 :
  find_mult_3 7766553322 = [55510, 766553322] := sorry

/-
info: [4, 63]
-/
-- #guard_msgs in
-- #eval find_mult_3 362

/-
info: [25, 6630]
-/
-- #guard_msgs in
-- #eval find_mult_3 6063

/-
info: [55510, 766553322]
-/
-- #guard_msgs in
-- #eval find_mult_3 7766553322

-- Apps difficulty: introductory
-- Assurance level: unguarded