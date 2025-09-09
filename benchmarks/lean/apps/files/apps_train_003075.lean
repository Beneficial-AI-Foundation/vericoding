/-
## MTV Cribs is back!

![](https://s-media-cache-ak0.pinimg.com/236x/1b/cf/f4/1bcff4f4621644461103576e40bde4ed.jpg)

_If you haven't solved it already I recommend trying [this kata](https://www.codewars.com/kata/5834a44e44ff289b5a000075) first._

## Task

Given `n` representing the number of floors build a penthouse like this:

```
        ___
       /___\                
      /_____\
      |  _  |     1 floor
      |_|_|_|

       _____
      /_____\
     /_______\
    /_________\             
   /___________\
   |           |
   |    ___    |     2 floors
   |   |   |   |
   |___|___|___|

      _______
     /_______\
    /_________\
   /___________\
  /_____________\
 /_______________\
/_________________\
|                 |         3 floors
|                 |
|      _____      |
|     |     |     |
|     |     |     |
|_____|_____|_____|

```

**Note:** whitespace should be preserved on both sides of the roof. No invalid input tests.

Good luck!
-/

def my_crib (n : Nat) : String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def splitLines (s : String) : List String :=
  sorry

theorem crib_width_consistency {n : Nat} (h : 1 ≤ n ∧ n ≤ 10) :
  let width := 4 + 3 + 6 * (n - 1)
  let lines := splitLines (my_crib n)
  ∀ line ∈ lines, line.length = width :=
sorry

theorem crib_roof_top {n : Nat} (h : 1 ≤ n ∧ n ≤ 10) :
  let lines := splitLines (my_crib n)
  let first_line := lines.head?
  ∀ line, first_line = some line → line.replace " " "" = line.replace "_" "" :=
sorry

theorem crib_sloping_roof {n : Nat} (h : 1 ≤ n ∧ n ≤ 10) :
  let lines := splitLines (my_crib n)
  let roof_lines := lines.take (3 + 2*(n-1))
  ∀ line ∈ roof_lines, (line.contains '/') ∧ (line.contains '\\') :=
sorry

theorem crib_wall_structure {n : Nat} (h : 1 ≤ n ∧ n ≤ 10) :
  let lines := splitLines (my_crib n)
  let wall_lines := lines.drop (3 + 2*(n-1))
  ∀ line ∈ wall_lines, line.startsWith "|" ∧ line.endsWith "|" :=
sorry

theorem crib_bottom_line {n : Nat} (h : 1 ≤ n ∧ n ≤ 10) :
  let lines := splitLines (my_crib n)
  ∀ last_line, lines.getLast? = some last_line → last_line.contains '_' :=
sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval my_crib 1

/-
info: expected2
-/
-- #guard_msgs in
-- #eval my_crib 2

/-
info: expected3
-/
-- #guard_msgs in
-- #eval my_crib 3

-- Apps difficulty: introductory
-- Assurance level: unguarded