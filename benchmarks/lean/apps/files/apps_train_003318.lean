/-
A [perfect power](https://en.wikipedia.org/wiki/Perfect_power) is a classification of positive integers:

> In mathematics, a **perfect power** is a positive integer that can be expressed as an integer power of another positive integer. More formally, n is a perfect power if there exist natural numbers m > 1, and k > 1 such that m^(k) = n.

Your task is to check wheter a given integer is a perfect power. If it is a perfect power, return a pair `m` and `k` with m^(k) = n as a proof. Otherwise return `Nothing`, `Nil`, `null`, `NULL`, `None` or your language's equivalent.

**Note:** For a perfect power, there might be several pairs. For example `81 = 3^4 = 9^2`, so `(3,4)` and `(9,2)` are valid solutions. However, the tests take care of this, so if a number is a perfect power, return any pair that proves it.

### Examples
```python
isPP(4) => [2,2]
isPP(9) => [3,2]
isPP(5) => None
```
-/

-- <vc-helpers>
-- </vc-helpers>

def isPP (n : Nat) : Option (Nat × Nat) :=
  sorry

theorem isPP_properties {n : Nat} (h : n > 0) :
  match isPP n with
  | none => 
    ∀ b e, b ≥ 2 → e ≥ 2 → b ^ e ≠ n
  | some (b, e) =>
    b ≥ 2 ∧ e ≥ 2 ∧ b ^ e = n
  := sorry

theorem isPP_perfect_powers {base exp : Nat} 
  (hbase : base ≥ 2) (hexp : exp ≥ 2) :
  ∃ b e, 
    isPP (base ^ exp) = some (b, e) ∧
    b ^ e = base ^ exp
  := sorry

/-
info: [2, 2]
-/
-- #guard_msgs in
-- #eval isPP 4

/-
info: [3, 2]
-/
-- #guard_msgs in
-- #eval isPP 9

/-
info: None
-/
-- #guard_msgs in
-- #eval isPP 5

-- Apps difficulty: introductory
-- Assurance level: unguarded