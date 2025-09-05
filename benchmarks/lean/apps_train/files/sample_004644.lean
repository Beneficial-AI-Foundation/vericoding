Given a certain array of integers, create a function that may give the minimum number that may be divisible for all the numbers of the array.

```python
min_special_mult([2, 3 ,4 ,5, 6, 7]) == 420
```
The array may have integers that occurs more than once:
```python
min_special_mult([18, 22, 4, 3, 21, 6, 3]) == 2772
```
The array should have all its elements integer values. If the function finds an invalid entry (or invalid entries) like strings of the alphabet or symbols will not do the calculation and will compute and register them, outputting a message in singular or plural, depending on the number of invalid entries.

```python
min_special_mult([16, 15, 23, 'a', '&', '12']) == "There are 2 invalid entries: ['a', '&']"

min_special_mult([16, 15, 23, 'a', '&', '12', 'a']) == "There are 3 invalid entries: ['a', '&', 'a']"

min_special_mult([16, 15, 23, 'a', '12']) == "There is 1 invalid entry: a"
```
If the string is a valid number, the function will convert it as an integer.
```python
min_special_mult([16, 15, 23, '12']) == 5520

min_special_mult([16, 15, 23, '012']) == 5520
```
All the `None`/`nil` elements of the array will be ignored:
```python
min_special_mult([18, 22, 4, , None, 3, 21, 6, 3]) == 2772
```
If the array has a negative number, the function will convert to a positive one.
```python
min_special_mult([18, 22, 4, , None, 3, -21, 6, 3]) == 2772

min_special_mult([16, 15, 23, '-012']) == 5520
```

Enjoy it

def min_special_mult (numbers : List Int) : Int ⊕ String := sorry

theorem valid_numbers_only (numbers : List Int) 
  (h : ∀ n ∈ numbers, n > 0)
  : ∃ result, (min_special_mult numbers = Sum.inl result ∧ result > 0) := sorry

/-- Helper function to convert strings to a list containing each character -/

def stringToList (s : String) : List Char := s.data

def stringContains (s₁ s₂ : String) : Prop := ∃ pre post : String, s₁ = pre ++ s₂ ++ post

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
