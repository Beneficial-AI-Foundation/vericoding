/-
=====Problem Statement=====
You are given a positive integer N.
Your task is to print a palindromic triangle of size N.

For example, a palindromic triangle of size 5 is:
1
121
12321
1234321
123454321

You can't take more than two lines. The first line (a for-statement) is already written for you.
You have to complete the code using exactly one print statement.

Note:
Using anything related to strings will give a score of 0.
Using more than one for-statement will give a score of 0.

=====Input Format=====
A single line of input containing the integer N.

=====Constraints=====
0<N<10

=====Output Format=====
Print the palindromic triangle of size N as explained above.
-/

def make_palindrome_triangle (n: Nat) : String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def split_lines (s: String) : List String :=
  sorry

theorem palindrome_triangle_line_count {n: Nat} (h: 0 < n) (h2: n ≤ 9):
  let lines := split_lines (make_palindrome_triangle n)
  lines.length = n :=
sorry

theorem palindrome_triangle_lines_are_palindromes {n: Nat} (h: 0 < n) (h2: n ≤ 9):
  let lines := split_lines (make_palindrome_triangle n)
  ∀ line ∈ lines, line.data = (line.data.reverse) :=
sorry

theorem palindrome_triangle_lines_increase {n: Nat} (h: 0 < n) (h2: n ≤ 9):
  let lines := split_lines (make_palindrome_triangle n)
  ∀ i, 0 < i → i < lines.length → (lines.get! i).length > (lines.get! (i-1)).length :=
sorry

theorem palindrome_triangle_first_line {n: Nat} (h: 0 < n) (h2: n ≤ 9):
  let lines := split_lines (make_palindrome_triangle n)
  lines.head! = "1" :=
sorry

theorem palindrome_triangle_only_digits {n: Nat} (h: 0 < n) (h2: n ≤ 9):
  let lines := split_lines (make_palindrome_triangle n)
  ∀ line ∈ lines, ∀ c ∈ line.data, '0' ≤ c ∧ c ≤ '9' :=
sorry

theorem palindrome_triangle_middle_increment {n: Nat} (h: 0 < n) (h2: n ≤ 9):
  let lines := split_lines (make_palindrome_triangle n)
  ∀ i, 0 < i → i < lines.length →
    let line := lines.get! i
    let mid := line.length / 2
    ∀ j, j < mid → line.data[j]! = Char.ofNat ((j + 1) + '0'.toNat) :=
sorry

/-
info: '1\n121\n12321'
-/
-- #guard_msgs in
-- #eval make_palindrome_triangle 3

/-
info: '1\n121\n12321\n1234321\n123454321'
-/
-- #guard_msgs in
-- #eval make_palindrome_triangle 5

/-
info: '1'
-/
-- #guard_msgs in
-- #eval make_palindrome_triangle 1

-- Apps difficulty: introductory
-- Assurance level: unguarded