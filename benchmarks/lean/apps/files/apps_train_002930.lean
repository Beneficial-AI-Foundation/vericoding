-- <vc-preamble>
def polydivisible (n : Nat) : Bool := sorry

def digits (n : Nat) : List Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def take_prefix (n : Nat) (len : Nat) : Nat := sorry

theorem polydivisible_characterization {n : Nat} :
  polydivisible n ↔ 
  (∀ i : Nat, i > 0 ∧ i ≤ (digits n).length → 
    take_prefix n i % i = 0) := sorry

theorem single_digit_polydivisible {n : Nat} :
  n > 0 ∧ n < 10 → polydivisible n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem polydivisible_positive {n : Int} :
  n ≤ 0 → polydivisible n.toNat = false := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval polydivisible 1232

/-
info: False
-/
-- #guard_msgs in
-- #eval polydivisible 123220

/-
info: True
-/
-- #guard_msgs in
-- #eval polydivisible 987654
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded