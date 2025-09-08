/-
In this Kata, you will be given a string and your task will be to return a list of ints detailing the count of uppercase letters, lowercase, numbers and special characters, as follows.

```Haskell
Solve("*'&ABCDabcde12345") = [4,5,5,3]. 
--the order is: uppercase letters, lowercase, numbers and special characters.
```

More examples in the test cases. 

Good luck!
-/

-- <vc-helpers>
-- </vc-helpers>

def solve (s : String) : Array Nat := sorry

theorem solve_returns_four_nonnegative : ∀ s : String,
  let result := solve s
  (result.size = 4) ∧ 
  (∀ i, i < result.size → 0 ≤ result[i]!) := sorry

theorem solve_categorizes_correctly : ∀ s : String,
  let result := solve s;
  result.size = 4 ∧
  (result[0]! = (s.data.filter Char.isUpper).length) ∧
  (result[1]! = (s.data.filter Char.isLower).length) ∧
  (result[2]! = (s.data.filter Char.isDigit).length) ∧
  (result[3]! = (s.data.filter (fun c => !(Char.isAlphanum c))).length) := sorry

theorem solve_all_uppercase : ∀ s : String,
  s.data.all Char.isUpper →
  let result := solve s;
  result.size = 4 ∧
  (result[0]! = s.length) ∧
  (result[1]! = 0) ∧
  (result[2]! = 0) ∧
  (result[3]! = 0) := sorry

theorem solve_all_lowercase : ∀ s : String,
  s.data.all Char.isLower →
  let result := solve s;
  result.size = 4 ∧
  (result[0]! = 0) ∧
  (result[1]! = s.length) ∧
  (result[2]! = 0) ∧
  (result[3]! = 0) := sorry

theorem solve_all_numbers : ∀ s : String,
  s.data.all Char.isDigit →
  let result := solve s;
  result.size = 4 ∧
  (result[0]! = 0) ∧
  (result[1]! = 0) ∧
  (result[2]! = s.length) ∧
  (result[3]! = 0) := sorry

/-
info: [1, 18, 3, 2]
-/
-- #guard_msgs in
-- #eval solve "Codewars@codewars123.com"

/-
info: [7, 6, 3, 2]
-/
-- #guard_msgs in
-- #eval solve "bgA5<1d-tOwUZTS8yQ"

/-
info: [9, 9, 6, 9]
-/
-- #guard_msgs in
-- #eval solve "P*K4%>mQUDaG$h=cx2?.Czt7!Zn16p@5H"

-- Apps difficulty: introductory
-- Assurance level: guarded