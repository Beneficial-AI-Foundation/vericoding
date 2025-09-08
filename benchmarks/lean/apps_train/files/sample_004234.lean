/-
Write a function that takes a string and returns an array of the repeated characters (letters, numbers, whitespace) in the string.

If a charater is repeated more than once, only show it once in the result array.

Characters should be shown **by the order of their first repetition**. Note that this may be different from the order of first appearance of the character.

Characters are case sensitive.

For F# return a "char list"

## Examples:

```python
remember("apple") => returns ["p"]
remember("apPle") => returns []          # no repeats, "p" != "P"
remember("pippi") => returns ["p","i"]   # show "p" only once
remember('Pippi') => returns ["p","i"]   # "p" is repeated first
```
-/

-- <vc-helpers>
-- </vc-helpers>

def remember (s : String) : List Char := sorry

theorem remember_chars_in_input (s : String) : 
  ∀ c ∈ remember s, c ∈ s.data := by sorry

theorem remember_only_duplicates (s : String) :
  ∀ c ∈ remember s, (s.data.count c) > 1 := by sorry

theorem remember_no_duplicates (s : String) :
  (remember s).Nodup := by sorry

theorem remember_maintains_order (s : String) (i j : Nat) 
  (h₁ : i < j) (h₂ : i < (remember s).length) (h₃ : j < (remember s).length) :
  let c₁ := (remember s)[i]'h₂
  let c₂ := (remember s)[j]'h₃
  let pos₁ := s.data.indexOf c₁
  let pos₂ := s.data.indexOf c₂
  pos₁ ≤ pos₂ := by sorry

theorem remember_empty (s : String) : 
  s = "" → remember s = [] := by sorry

theorem remember_length_bound (s : String) :
  (remember s).length ≤ s.length / 2 := by sorry

theorem remember_returns_chars (s : String) :
  ∀ c ∈ remember s, c.toString.length = 1 := by sorry

-- Apps difficulty: introductory
-- Assurance level: guarded