/-
We'll create a function that takes in two parameters:

* a sequence (length and types of items are irrelevant)
* a function (value, index) that will be called on members of the sequence and their index. The function will return either true or false.

Your function will iterate through the members of the sequence in order until the provided function returns true; at which point your function will return that item's **index**. 

If the function given returns false for all members of the sequence, your function should return -1.

```python
true_if_even = lambda value, index: value % 2 == 0
find_in_array([1,3,5,6,7], true_if_even) # --> 3
```
-/

-- <vc-helpers>
-- </vc-helpers>

def find_in_array {α : Type} [Inhabited α] (arr : List α) (pred : α → Nat → Bool) : Int := sorry

theorem find_specific_value {α : Type} [Inhabited α] [BEq α] (arr : List α) (target : α) :
  let result := find_in_array arr (fun x _ => x == target)
  result ≠ -1 → (result.toNat < arr.length ∧ arr[result.toNat]! = target) ∧
  result = -1 → ∀ x ∈ arr, x ≠ target := sorry

theorem find_at_index {α : Type} [Inhabited α] (arr : List α) (index : Nat) :
  let result := find_in_array arr (fun _ i => i == index)
  result ≠ -1 → result.toNat = index ∧
  result = -1 → index ≥ arr.length := sorry

theorem first_match_returned {α : Type} [Inhabited α] (arr : List α) :
  let result := find_in_array arr (fun _ _ => true)
  (arr.length > 0 → result = 0) ∧
  (arr.length = 0 → result = -1) := sorry

theorem no_match_returns_negative {α : Type} [Inhabited α] (arr : List α) :
  find_in_array arr (fun _ _ => false) = -1 := sorry

theorem index_matches_value [Inhabited Int] (arr : List Int) :
  let result := find_in_array arr (fun x i => x.toNat = i)
  result ≠ -1 → arr[result.toNat]!.toNat = result.toNat ∧
  result = -1 → ∀ (i : Nat), i < arr.length → arr[i]!.toNat ≠ i := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_in_array [1, 3, 5, 6, 7] lambda value, index: value % 2 == 0

/-
info: -1
-/
-- #guard_msgs in
-- #eval find_in_array [1, 2, 3, 4, 5] lambda value, index: value == 10

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_in_array [5, 4, 2, 3, 4] lambda value, index: value == index

-- Apps difficulty: introductory
-- Assurance level: unguarded