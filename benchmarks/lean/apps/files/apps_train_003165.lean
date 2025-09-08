/-
>When no more interesting kata can be resolved, I just choose to create the new kata, to solve their own, to enjoy the process  --myjinxin2015 said

# Description:
 Give you two number `m` and `n`(two positive integer, m < n), make a triangle pattern with number sequence `m to n`. The order is clockwise, starting from the top corner, like this:

```
 When m=1 n=10  triangle is:
    1
   9 2
  8 0 3
 7 6 5 4
```
 Note: The pattern only uses the last digit of each number; Each row separated by "\n"; Each digit separated by a space; Left side may need pad some spaces, but don't pad the right side; If `m to n` can not make the triangle, return `""`.

# Some examples:

```
makeTriangle(1,3) should return:
 1
3 2

makeTriangle(6,20) should return: 

    6
   7 7
  6 8 8
 5 0 9 9
4 3 2 1 0

makeTriangle(1,12) should return ""

```
-/

def make_triangle (m n : Nat) : String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def isDigitChar (c : Char) : Bool :=
  '0' ≤ c ∧ c ≤ '9'

theorem make_triangle_valid_output_type {m n : Nat} :
  ∀ r : String, r = make_triangle m n → (r = "" ∨ String.contains r '\n') :=
  sorry

theorem make_triangle_digits_only {m n : Nat} (h : m ≤ n) (h2 : n - m + 1 ≤ 45) :
  ∀ c : Char, c ∈ (make_triangle m n).toList → 
    (c = ' ' ∨ c = '\n' ∨ isDigitChar c) :=
  sorry

theorem make_triangle_row_growth {m n : Nat} (h : m ≤ n) (h2 : n - m + 1 ≤ 45) :
  let lines := String.split (make_triangle m n) (· = '\n')
  ∀ i : Nat, i < lines.length →
    ∀ h : i < lines.length,
    (String.split (String.trim (lines[i]'h)) (· = ' ')).length = i + 1 :=
  sorry

theorem make_triangle_total_elements {m n : Nat} (h : m ≤ n) :
  let size := n - m + 1
  let result := make_triangle m n
  let lines := String.split result (· = '\n')
  result ≠ "" →
  (lines.foldl (fun acc line => 
    acc + (String.split (String.trim line) (· = ' ')).length) 0) = size :=
  sorry

theorem make_triangle_invalid_empty {m n : Nat} :
  (m > n ∨ n - m + 1 > 45) → make_triangle m n = "" :=
  sorry

-- Apps difficulty: introductory
-- Assurance level: guarded