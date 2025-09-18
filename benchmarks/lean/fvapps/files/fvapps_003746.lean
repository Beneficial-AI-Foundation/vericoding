-- <vc-preamble>
def square_digits (n : Nat) : Nat := sorry

def digits_to_nat (digits : List Nat) : Nat := sorry

def nat_to_digits (n : Nat) : List Nat := sorry

def square_len (n : Nat) : Nat := toString (n * n) |>.length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def listSum : List Nat → Nat 
| [] => 0
| x :: xs => x + listSum xs
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible