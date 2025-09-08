/-
Create a function that takes a positive integer and returns the next bigger number that can be formed by rearranging its digits. For example:

```
12 ==> 21
513 ==> 531
2017 ==> 2071
```

If the digits can't be rearranged to form a bigger number, return `-1` (or `nil` in Swift):

```
9 ==> -1
111 ==> -1
531 ==> -1
```
-/

def digits (n : Nat) : List Nat := sorry
def digits_sorted (n : Nat) : List Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def digits_sorted_desc (n : Nat) : List Nat := sorry

def next_bigger (n : Nat) : Int := sorry

theorem next_bigger_larger (n : Nat) : 
  let result := next_bigger n
  result ≠ -1 → result > n := sorry

theorem next_bigger_same_digits (n : Nat) :
  let result := next_bigger n
  result ≠ -1 → 
  ∀ (r : Nat), result = r → (digits_sorted n = digits_sorted r) := sorry

theorem next_bigger_minimal (n : Nat) :
  let result := next_bigger n
  result ≠ -1 →
  ∀ x, n < x → x < result → digits_sorted x ≠ digits_sorted n := sorry

theorem next_bigger_none_exists (n : Nat) :
  next_bigger n = -1 ↔ digits n = digits_sorted_desc n := sorry

theorem next_bigger_single_digit (n : Nat) :
  n < 10 → next_bigger n = -1 := sorry

theorem next_bigger_output_type (n : Nat) :
  ∃ i : Int, next_bigger n = i := sorry

/-
info: 21
-/
-- #guard_msgs in
-- #eval next_bigger 12

/-
info: 531
-/
-- #guard_msgs in
-- #eval next_bigger 513

/-
info: 2071
-/
-- #guard_msgs in
-- #eval next_bigger 2017

/-
info: -1
-/
-- #guard_msgs in
-- #eval next_bigger 9876543210

-- Apps difficulty: interview
-- Assurance level: unguarded