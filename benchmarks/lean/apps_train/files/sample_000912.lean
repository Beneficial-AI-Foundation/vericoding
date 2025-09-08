/-
Chef loves lucky numbers. Everybody knows that lucky numbers are positive integers whose decimal representation contains only the lucky digits 4 and 7. For example, numbers 47, 744, 4 are lucky and 5, 17, 467 are not.

Let F(X) equals to the number of lucky digits in decimal representation of X. Chef wants to know the number of such integers X, that L ≤ X ≤ R and F(X) is a lucky number. Help him and calculate that number modulo 109+7.

-----Input-----
First line contains one integer T, the number of test cases. Each of the following T lines contains two space separated positive integers L and R.

-----Output-----
For each of the T test cases print one integer, the number of such X, that L ≤ X ≤ R and F(X) is a lucky number, modulo 1000000007.

-----Constraints-----

1 ≤ T ≤ 10

1 ≤ L ≤ R ≤ 101000

-----Example-----
Input:
4
1 100
1 10000
1 100000
4444 4447

Output:
0
16
640
2

-----Notes-----
First test case: of course, any number of less than 4 digits can't contain lucky number of lucky digits, so the answer is 0.

Second test case: 16 required numbers are 4444 4447 4474 4477 4744 4747 4774 4777 7444 7447 7474 7477 7744 7747 7774 7777.

Third test case: there are 640 required lucky numbers. Some of them are 4474, 14747, 41474, 77277, 44407, 74749.

Fourth test case: the only two required numbers are 4444 and 4447.
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_lucky_numbers (left right : String) : Nat := sorry

theorem solve_lucky_numbers_range {left right : String} 
  (h1 : ∀ c ∈ left.data, c.isDigit)
  (h2 : ∀ c ∈ right.data, c.isDigit)
  (h3 : left.length > 0)
  (h4 : right.length > 0)
  (h5 : left.toNat? = some (l : Nat))
  (h6 : right.toNat? = some (r : Nat))
  (h7 : l ≤ 10^9)
  (h8 : r ≤ 10^9)
  : solve_lucky_numbers left right ≤ 10^9 + 7 := sorry

theorem solve_lucky_numbers_identical_input {n : String}
  (h1 : ∀ c ∈ n.data, c.isDigit) 
  (h2 : n.length > 0)
  (h3 : n.toNat? = some (num : Nat))
  (h4 : num ≤ 10^9)
  : solve_lucky_numbers n n ≤ 1 := sorry

theorem solve_lucky_numbers_invalid_input_left {n right : String}
  (h1 : ∃ c ∈ n.data, !c.isDigit)
  (h2 : ∀ c ∈ right.data, c.isDigit)
  : solve_lucky_numbers n right = 0 := sorry

theorem solve_lucky_numbers_invalid_input_right {left n : String}
  (h1 : ∀ c ∈ left.data, c.isDigit)
  (h2 : ∃ c ∈ n.data, !c.isDigit)
  : solve_lucky_numbers left n = 0 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_lucky_numbers "1" "100"

/-
info: 16
-/
-- #guard_msgs in
-- #eval solve_lucky_numbers "1" "10000"

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_lucky_numbers "4444" "4447"

-- Apps difficulty: interview
-- Assurance level: guarded