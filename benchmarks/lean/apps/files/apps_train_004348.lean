/-
Complete the solution. It should try to retrieve the value of the array at the index provided. If the index is out of the array's max bounds then it should return the default value instead. 

Example:
```Haskell
solution [1..3] 1 1000 `shouldBe` 2
solution [1..5] (10) 1000 `shouldBe` 1000
-- negative values work as long as they are not out of the length bounds
solution [1..3] (-1) 1000 `shouldBe` 3
solution [1..3] (-5) 1000 `shouldBe` 1000
solution [1..3] (-3) 1000 `shouldBe` 1
solution [1..5] (-3) 1000 `shouldBe` 3
-- for Haskell default value will always be a (random) number, not a character.
```

```python
data = ['a', 'b', 'c']
solution(data, 1, 'd') # should == 'b'
solution(data, 5, 'd') # should == 'd'

# negative values work as long as they aren't out of the length bounds
solution(data, -1, 'd') # should == 'c'
solution(data, -5, 'd') # should == 'd'
```
-/

-- <vc-helpers>
-- </vc-helpers>

def solution {α : Type} [Inhabited α] (items : List α) (index : Int) (default : α) : α := sorry

theorem solution_in_bounds {α : Type} [Inhabited α] (items : List α) (index : Int) (default : α) :
  (0 ≤ index ∧ index < items.length) → 
  solution items index default = items.get! index.toNat := sorry

theorem solution_negative_in_bounds {α : Type} [Inhabited α] (items : List α) (index : Int) (default : α) :
  (-items.length ≤ index ∧ index < 0) → 
  solution items index default = items.get! (items.length + index.toNat) := sorry

theorem solution_out_of_bounds {α : Type} [Inhabited α] (items : List α) (index : Int) (default : α) :
  (index < -items.length ∨ index ≥ items.length) → 
  solution items index default = default := sorry

theorem empty_list {α : Type} [Inhabited α] (default : α) :
  ∀ (index : Int), solution ([] : List α) index default = default := sorry

theorem list_bounds {α : Type} [Inhabited α] (items : List α) (default : α) 
  (h : items ≠ []) :
  solution items items.length default = default ∧
  solution items (-items.length - 1) default = default ∧
  solution items (items.length - 1) default = items.getLast h ∧
  solution items (-items.length) default = items.head! := sorry

/-
info: 'b'
-/
-- #guard_msgs in
-- #eval solution ["a", "b", "c"] 1 "d"

/-
info: 'd'
-/
-- #guard_msgs in
-- #eval solution ["a", "b", "c"] 5 "d"

/-
info: 'c'
-/
-- #guard_msgs in
-- #eval solution ["a", "b", "c"] -1 "d"

/-
info: 'd'
-/
-- #guard_msgs in
-- #eval solution ["a", "b", "c"] -5 "d"

-- Apps difficulty: introductory
-- Assurance level: unguarded