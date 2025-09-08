/-
A format for expressing an ordered list of integers is to use a comma separated list of either

* individual integers
* or a range of integers denoted by the starting integer separated from the end integer in the range by a dash, '-'. The range includes all integers in the interval including both endpoints.  It is not considered a range unless it spans at least 3 numbers. For example "12,13,15-17"

Complete the solution  so that it takes a list of integers in increasing order and returns a correctly formatted string in the range format. 

**Example:**

```python
solution([-6, -3, -2, -1, 0, 1, 3, 4, 5, 7, 8, 9, 10, 11, 14, 15, 17, 18, 19, 20])
# returns "-6,-3-1,3-5,7-11,14,15,17-20"
```

```C#
RangeExtraction.Extract(new[] {-6, -3, -2, -1, 0, 1, 3, 4, 5, 7, 8, 9, 10, 11, 14, 15, 17, 18, 19, 20});
# returns "-6,-3-1,3-5,7-11,14,15,17-20"
```

*Courtesy of rosettacode.org*
-/

def solution (xs : List Int) : String := sorry

theorem solution_empty_list : solution [] = "" := by sorry

def parseAsInt (s : String) : Option Int := sorry

inductive ValidPart : Type where
  | empty : ValidPart
  | single (n : Int) : ValidPart
  | range (s e : Int) (h : s < e) : ValidPart

-- <vc-helpers>
-- </vc-helpers>

def isValidPart (s : String) : Bool := sorry 

theorem solution_valid_parts (xs : List Int) :
  ∀ p ∈ (solution xs).splitOn ",", isValidPart p = true := by sorry

theorem solution_nonempty_input (xs : List Int) (h : xs ≠ []) :
  solution xs ≠ "" := by sorry

/-
info: '-6,-3-1,3-5,7-11,14,15,17-20'
-/
-- #guard_msgs in
-- #eval solution [-6, -3, -2, -1, 0, 1, 3, 4, 5, 7, 8, 9, 10, 11, 14, 15, 17, 18, 19, 20]

/-
info: '-3--1,2,10,15,16,18-20'
-/
-- #guard_msgs in
-- #eval solution [-3, -2, -1, 2, 10, 15, 16, 18, 19, 20]

/-
info: '1-5'
-/
-- #guard_msgs in
-- #eval solution [1, 2, 3, 4, 5]

-- Apps difficulty: interview
-- Assurance level: unguarded