/-
Welcome. In this kata, you are asked to square every digit of a number and concatenate them.

For example, if we run 9119 through the function, 811181 will come out, because 9^(2) is 81 and 1^(2) is 1.

**Note:** The function accepts an integer and returns an integer
-/

def square_digits (n : Nat) : Nat := sorry

def digits_to_nat (digits : List Nat) : Nat := sorry

def nat_to_digits (n : Nat) : List Nat := sorry

def square_len (n : Nat) : Nat := toString (n * n) |>.length

-- <vc-helpers>
-- </vc-helpers>

def listSum : List Nat → Nat 
| [] => 0
| x :: xs => x + listSum xs

theorem single_digit_square {d : Nat} (h : d ≤ 9) :
  square_digits d = d * d :=
sorry

/-
info: 9414
-/
-- #guard_msgs in
-- #eval square_digits 3212

/-
info: 4114
-/
-- #guard_msgs in
-- #eval square_digits 2112

/-
info: 811181
-/
-- #guard_msgs in
-- #eval square_digits 9119

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible