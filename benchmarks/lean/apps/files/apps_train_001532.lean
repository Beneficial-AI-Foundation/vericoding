/-
Write a program that reads numbers until -1 is not given.
The program finds how many of the given numbers are more than 30, $N$.
It also finds the average weighted sum of even numbers, $A$.
The weight of the $i$th number is defined as the position of the number (1 based indexing) times the number. To find the average weighted sum, you need to add all these weights for the even numbers, then divide the sum by the sum of the positions of the numbers.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains some numbers, terminated by -1

-----Output:-----
For each testcase, output in a single line the count of numbers that are greater than 30, $N$, and the average weighted sum of the even numbers, $A$, separated by a space. Make sure to set the precision of the average weighted sum to 2 places after the decimal point.

-----Constraints-----
- $1 \leq T \leq 1000$
- $2 \leq N \leq 1000$

-----Sample Input:-----
1
33 100 77 42 12 -1

-----Sample Output:-----
4 38.91

-----EXPLANATION:-----
In the series of numbers 33 100 77 42 12 -1, the count of numbers greater than 30 is 4
The average weighted sum of the even numbers is given by:
((2 * 100) + (4 * 42) + (5 * 12)) / (2 + 4 + 5)
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_weighted_sum (numbers : List Int) : Int × Float := sorry

theorem no_great_numbers {nums : List Int} (h : ∀ n ∈ nums, n ≤ 30) :
  (solve_weighted_sum (nums ++ [-1])).1 = 0 := sorry

theorem all_great_numbers {nums : List Int} (h : ∀ n ∈ nums, n > 30) :
  (solve_weighted_sum (nums ++ [-1])).1 = nums.length := sorry

theorem average_bounds {nums : List Int} (h : ∀ n ∈ nums, n ≥ 0) : 
  let avg := (solve_weighted_sum (nums ++ [-1])).2
  avg = 0 ∨ avg ≥ 0 := sorry

-- Apps difficulty: interview
-- Assurance level: guarded