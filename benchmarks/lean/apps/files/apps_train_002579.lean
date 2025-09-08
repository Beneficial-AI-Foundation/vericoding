/-
# One is the loneliest number

## Task

The range of vision of a digit is its own value. `1` can see one digit to the left and one digit to the right,` 2` can see two digits, and so on.

Thus, the loneliness of a digit `N` is the sum of the digits which it can see.

Given a non-negative integer, your funtion must determine if there's at least one digit `1` in this integer such that its loneliness value is minimal.

## Example

```
number = 34315
```

digit | can see on the left | can see on the right | loneliness
--- | --- | --- | ---
3 | - | 431 | 4 + 3 + 1 = 8
4 | 3 | 315 | 3 + 3 + 1 + 5 = 12
3 | 34 | 15 | 3 + 4 + 1 + 5 = 13
1 | 3 | 5 | 3 + 5 = 8
5 | 3431 | - | 3 + 4 + 3 + 1 = 11

Is there a `1` for which the loneliness is minimal? Yes.
-/

def digits (n: Nat) : List Nat := sorry
def visible_sum (n i: Nat) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def min_visible_sum (n: Nat) : Nat := sorry
def loneliest (n: Nat) : Bool := sorry

theorem loneliest_returns_bool (n: Nat) :
  loneliest n = true ∨ loneliest n = false := sorry

theorem loneliest_zero_one : 
  ∀ n: Nat, (∀ d: Nat, d ∈ (digits n) → d = 0 ∨ d = 1) →
  loneliest n = true ↔ ∃ i, (digits n).get? i = some 1 ∧ 
  (∀ j, j ≠ i → (digits n).get? j = some 0) := sorry

theorem loneliest_same_digit :
  ∀ n: Nat, (∀ i j: Nat, i < (digits n).length → j < (digits n).length → 
    (digits n).get ⟨i, sorry⟩ = (digits n).get ⟨j, sorry⟩) →
  loneliest n = true ↔ (digits n).get ⟨0, sorry⟩ = 1 := sorry

theorem loneliest_no_ones :
  ∀ n: Nat, (∀ i: Nat, i < (digits n).length → (digits n).get ⟨i, sorry⟩ ≠ 1) →
  loneliest n = false := sorry

theorem loneliest_min_loneliness :
  ∀ n: Nat, loneliest n = true ↔ 
  (∃ i: Nat, (digits n).get? i = some 1 ∧
   visible_sum n i = min_visible_sum n) := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval loneliest 34315

/-
info: False
-/
-- #guard_msgs in
-- #eval loneliest 8854778

/-
info: True
-/
-- #guard_msgs in
-- #eval loneliest 11111

-- Apps difficulty: introductory
-- Assurance level: unguarded