/-
Your team is writing a fancy new text editor and you've been tasked with implementing the line numbering.

Write a function which takes a list of strings and returns each line prepended by the correct number.

The numbering starts at 1. The format is `n: string`. Notice the colon and space in between.

**Examples:**

```python
number([]) # => []
number(["a", "b", "c"]) # => ["1: a", "2: b", "3: c"]
```
-/

-- <vc-helpers>
-- </vc-helpers>

def number (lines : List String) : List String := sorry 

theorem number_same_length (lines : List String) :
  (number lines).length = lines.length := sorry

theorem number_format_get {lines : List String} {i : Nat} (h : i < lines.length) :
  (number lines).get ⟨i, by {
    rw [number_same_length]
    exact h
  }⟩ = s!"{i+1}: {lines.get ⟨i, h⟩}" := sorry

theorem number_handles_all_strings {lines : List String} :
  number lines = List.map (fun i => s!"{i+1}: {lines.get ⟨i, by sorry⟩}") 
    (List.range lines.length) := sorry

theorem number_empty_input :
  number [] = [] := sorry

/-
info: []
-/
-- #guard_msgs in
-- #eval number []

/-
info: ['1: a', '2: b', '3: c']
-/
-- #guard_msgs in
-- #eval number ["a", "b", "c"]

/-
info: ['1: ', '2: ', '3: ']
-/
-- #guard_msgs in
-- #eval number ["", "", ""]

-- Apps difficulty: introductory
-- Assurance level: unguarded