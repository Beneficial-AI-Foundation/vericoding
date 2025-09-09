/-
You are given a list/array which contains only integers (positive and negative). Your job is to sum only the numbers that are the same and consecutive. The result should be one list.

Extra credit if you solve it in one line. You can assume there is never an empty list/array and there will always be an integer. 

Same meaning: 1 == 1

1 != -1

#Examples:

```
[1,4,4,4,0,4,3,3,1] # should return [1,12,0,4,6,1]

"""So as you can see sum of consecutives 1 is 1 
sum of 3 consecutives 4 is 12 
sum of 0... and sum of 2 
consecutives 3 is 6 ..."""

[1,1,7,7,3] # should return [2,14,3]
[-5,-5,7,7,12,0] # should return [-10,14,12,0]
```
-/

-- <vc-helpers>
-- </vc-helpers>

def sum_consecutives (xs : List Int) : List Int := sorry

theorem sum_consecutives_length 
  (xs : List Int) 
  (h : xs ≠ []) : 
  List.length (sum_consecutives xs) ≤ List.length xs :=
sorry

theorem sum_consecutives_preserves_elements
  (xs : List Int)
  (h : xs ≠ []) :
  List.foldl (· + ·) 0 (sum_consecutives xs) = List.foldl (· + ·) 0 xs :=
sorry

theorem single_element_unchanged 
  (xs : List Int)
  (h : List.length xs = 1) :
  sum_consecutives xs = xs :=
sorry

theorem identical_elements
  (n : Nat)
  (h : n > 0)
  (xs : List Int)
  (h2 : xs.length = n)
  (h3 : ∀ x ∈ xs, x = 0) :
  (sum_consecutives xs).length = 1 ∧ 
  (sum_consecutives xs).head! = List.foldl (· + ·) 0 xs :=
sorry

theorem alternating_elements_preserve_length
  (xs : List Int)
  (h : xs.length ≥ 2)
  (h2 : ∀ (i : Nat), i + 1 < xs.length → 
        xs.get! i ≠ xs.get! (i + 1)) :
  (sum_consecutives xs).length = xs.length :=
sorry

-- Apps difficulty: introductory
-- Assurance level: guarded