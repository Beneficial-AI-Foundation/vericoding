/-
	Three numbers A, B and C are the inputs. Write a program to find second largest among them.

-----Input-----

The first line contains an integer T, the total number of testcases. Then T lines follow, each line contains three integers A, B and C. 

-----Output-----
For each test case, display the second largest among A, B and C, in a new line.

-----Constraints-----
- 1 ≤ T ≤ 1000
- 1 ≤ A,B,C ≤ 1000000

-----Example-----
Input
3 
120 11 400
10213 312 10
10 3 450

Output

120
312
10
-/

-- <vc-helpers>
-- </vc-helpers>

def find_second_largest (l: List Int) : Int := sorry 

theorem find_second_largest_from_list {l: List Int} 
  (h1: l.length ≥ 3) 
  (h2: ∀ (x y: Int), x ∈ l → y ∈ l → x = y → x = y) :
  find_second_largest l ∈ l := sorry

theorem find_second_largest_less_than_max {l: List Int}
  (h1: l.length ≥ 3)
  (h2: ∀ (x y: Int), x ∈ l → y ∈ l → x = y → x = y) :
  ∃ x, x ∈ l ∧ x > find_second_largest l := sorry

theorem find_second_largest_greater_than_min {l: List Int}
  (h1: l.length ≥ 3)
  (h2: ∀ (x y: Int), x ∈ l → y ∈ l → x = y → x = y) :
  ∃ x, x ∈ l ∧ x < find_second_largest l := sorry

/-
info: 120
-/
-- #guard_msgs in
-- #eval find_second_largest [120, 11, 400]

/-
info: 312
-/
-- #guard_msgs in
-- #eval find_second_largest [10213, 312, 10]

/-
info: 10
-/
-- #guard_msgs in
-- #eval find_second_largest [10, 3, 450]

-- Apps difficulty: interview
-- Assurance level: guarded