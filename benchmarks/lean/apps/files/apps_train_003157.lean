def evil (n : Nat) : String := sorry

theorem evil_result_valid (n : Nat) : 
  (evil n = "It's Evil!") ∨ (evil n = "It's Odious!") := sorry

-- <vc-helpers>
-- </vc-helpers>

def countOnes (n : Nat) : Nat := 
  if n = 0 then 0
  else if n % 2 = 1 
  then countOnes (n / 2) + 1
  else countOnes (n / 2)

theorem evil_xor_property (n m : Nat) :
  let n_evil := evil n = "It's Evil!"
  let m_evil := evil m = "It's Evil!"
  let xor_evil := evil (n ^^^ m) = "It's Evil!"
  (n_evil = m_evil) = xor_evil := sorry

/-
info: "It's Odious!"
-/
-- #guard_msgs in
-- #eval evil 1

/-
info: "It's Odious!"
-/
-- #guard_msgs in
-- #eval evil 2

/-
info: "It's Evil!"
-/
-- #guard_msgs in
-- #eval evil 3

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible