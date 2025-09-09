/-
## Task

Given `n` representing the number of floors build a beautiful multi-million dollar mansions like the ones in the example below:

```
     /\
    /  \
   /    \
  /______\  number of floors 3
  |      |
  |      |
  |______|

     /\
    /  \
   /____\
   |    |   2 floors
   |____|

     /\
    /__\    1 floor
    |__|
```

**Note:** whitespace should be preserved on both sides of the roof. Number of floors will go up to 30. There will be no tests with invalid input.

If you manage to complete it, you can try a harder version [here](https://www.codewars.com/kata/58360d112fb0ba255300008b).

Good luck!
-/

-- <vc-helpers>
-- </vc-helpers>

def my_crib (n : Nat) : String := sorry

def splitLines (s : String) : List String :=
  s.splitOn "\n"

theorem crib_line_count (n : Nat) (h : 0 < n) :
  (splitLines (my_crib n)).length = 2 * n + 1 := sorry

theorem crib_roof_chars (n : Nat) (h : 0 < n) (i : Nat) (h2 : i < n) 
    (h3 : i < (splitLines (my_crib n)).length) :
  let lines := splitLines (my_crib n)
  let line := lines[i]'h3
  line.trim.data.get? 0 = some '/' ∧ 
  line.trim.data.getLast? = some '\\' := sorry

theorem crib_ceiling_chars (n : Nat) (h : 0 < n) 
    (h2 : n < (splitLines (my_crib n)).length) :
  let lines := splitLines (my_crib n)
  let line := lines[n]'h2
  line.data.get? 0 = some '/' ∧ 
  line.data.getLast? = some '\\' := sorry

theorem crib_wall_chars (n : Nat) (h : 0 < n) (i : Nat) 
    (h2 : n + 1 ≤ i) (h3 : i < 2*n)
    (h4 : i < (splitLines (my_crib n)).length) :
  let lines := splitLines (my_crib n)
  let line := lines[i]'h4
  line.data.get? 0 = some '|' ∧ 
  line.data.getLast? = some '|' := sorry

theorem crib_floor_chars (n : Nat) (h : 0 < n)
    (h2 : 2*n < (splitLines (my_crib n)).length) :
  let lines := splitLines (my_crib n)
  let line := lines[2*n]'h2
  line.data.get? 0 = some '|' ∧ 
  line.data.getLast? = some '|' := sorry

theorem crib_line_widths (n : Nat) (h : 0 < n)
    (i j : Nat) (hi : i < (splitLines (my_crib n)).length) 
    (hj : j < (splitLines (my_crib n)).length) :
  let lines := splitLines (my_crib n)
  (lines[i]'hi).data.length = (lines[j]'hj).data.length ∧
  (lines[i]'hi).data.length = 2*n + 2 := sorry

theorem crib_underscore_count (n : Nat) (h : 0 < n)
    (h2 : n < (splitLines (my_crib n)).length)
    (h3 : 2*n < (splitLines (my_crib n)).length) :
  let lines := splitLines (my_crib n)
  let ceiling := lines[n]'h2
  let floor := lines[2*n]'h3
  (List.filter (· = '_') ceiling.data).length = 2*n ∧
  (List.filter (· = '_') floor.data).length = 2*n := sorry

theorem crib_symmetry (n : Nat) (h : 0 < n) 
    (i : Nat) (h2 : i < (splitLines (my_crib n)).length) :
  let lines := splitLines (my_crib n)
  let line := lines[i]'h2
  ∃ s : List Char,
    s = line.data ∧
    s = (s.reverse.map (fun c => 
      if c = '\\' then '/' 
      else if c = '/' then '\\'
      else c)) := sorry

/-
info: test1
-/
-- #guard_msgs in
-- #eval my_crib 1

/-
info: test2
-/
-- #guard_msgs in
-- #eval my_crib 2

/-
info: test3
-/
-- #guard_msgs in
-- #eval my_crib 3

-- Apps difficulty: introductory
-- Assurance level: unguarded