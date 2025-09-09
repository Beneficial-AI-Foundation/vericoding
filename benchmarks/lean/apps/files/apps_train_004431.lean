def natToDigits (n : Nat) : List Nat :=
  if n < 10 then
    [n]
  else
    natToDigits (n / 10) ++ [n % 10]

def listMax (xs : List Nat) : Nat :=
  xs.foldl Nat.max 0

-- <vc-helpers>
-- </vc-helpers>

def self_descriptive (n : Nat) : Bool := sorry

theorem self_descriptive_correct_counts
    {n : Nat}
    (h : self_descriptive n = true) :
    ∀ i : Nat,
    i < (natToDigits n).length →
    (natToDigits n).count i = (natToDigits n).get! i := sorry

theorem self_descriptive_valid_indices
    {n : Nat}
    (h : self_descriptive n = true) :
    ∀ i : Nat,
    i < (natToDigits n).length →
    i ≤ listMax (natToDigits n) := sorry

theorem self_descriptive_single_digit
    {n : Nat}
    (h : n < 10) :
    self_descriptive n = false := sorry

theorem self_descriptive_first_digit
    {n : Nat}
    (h1 : (natToDigits n).get! 0 ≠ 0)
    (h2 : (natToDigits n).get! 0 > (natToDigits n).length - 1) :
    self_descriptive n = false := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval self_descriptive 21200

/-
info: True
-/
-- #guard_msgs in
-- #eval self_descriptive 3211000

/-
info: False
-/
-- #guard_msgs in
-- #eval self_descriptive 21230

-- Apps difficulty: introductory
-- Assurance level: unguarded