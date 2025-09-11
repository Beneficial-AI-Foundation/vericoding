-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def repeat_str (n : Nat) (s : String) : String := sorry

theorem repeat_str_length (n : Nat) (s : String) :
  (repeat_str n s).length = s.length * n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem repeat_str_repeat (n : Nat) (s : String) :
  repeat_str n s = String.join (List.replicate n s) := sorry

theorem repeat_str_zero (s : String) :
  repeat_str 0 s = "" := sorry

theorem repeat_str_one (s : String) :
  repeat_str 1 s = s := sorry

/-
info: 'aaaa'
-/
-- #guard_msgs in
-- #eval repeat_str 4 "a"

/-
info: 'hello hello hello '
-/
-- #guard_msgs in
-- #eval repeat_str 3 "hello "

/-
info: 'abcabc'
-/
-- #guard_msgs in
-- #eval repeat_str 2 "abc"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded