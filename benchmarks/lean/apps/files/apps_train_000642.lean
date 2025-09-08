/-
Raju has created a program to find the square root of a number. But his program can store only integers. Being a newbie, he didn't know about rounding the numbers. Hence his program returns the absolute value of the result if possible. For example, sqrt(3) = 1.73205080757……. His program will return 1
Given a number $N$, and it's integral square root $S$, His instructor will consider the answer correct if Difference between $N$ and the square of $S$ is within less than or equal to $X$% of $N$.

-----Input:-----
- First line contains $T$ no. of test cases and $X$ separated by space
- For every test case, a line contains an integer $N$

-----Output:-----
For every test case, print yes  if his programs return square root and (N-(S^2)) <= 0.01XN . For everything else, print no on a new line

-----Constraints-----
10 points:
- $1 \leq T \leq 10$
- $0\leq N \leq 10$
20 points:
- $1 \leq T \leq 30000$
- $-10^9 \leq N \leq 10^9$
70 points:
- $1 \leq T \leq 10^6$
- $-10^9 \leq N \leq 10^9$

-----Sample Input:-----
2 20
5
3

-----Sample Output:-----
yes
no

-----EXPLANATION:-----
In #1, sqrt(5) = 2.2360679775. Taking integral value, S = 2.

S2 = 4. Difference=1 which is within 20% of 5
In #1, sqrt(3) = 1.73205080757. Taking integral value, S = 1.

S2 = 1. Difference=2  which is not within 20% of 3
-/

-- <vc-helpers>
-- </vc-helpers>

def sqrt (n : Int) : Int := sorry

def check_sqrt_accuracy (scale tolerance : Int) (numbers : List Int) : List String := sorry

theorem length_preservation {scale tolerance : Int} {numbers : List Int}
  (h1 : 0 < tolerance) (h2 : tolerance ≤ 100) :
  List.length (check_sqrt_accuracy scale tolerance numbers) = List.length numbers := sorry

theorem valid_results {scale tolerance : Int} {numbers : List Int} 
  (h1 : 0 < tolerance) (h2 : tolerance ≤ 100) :
  ∀ x ∈ check_sqrt_accuracy scale tolerance numbers, x = "yes" ∨ x = "no" := sorry

theorem negative_numbers_no {scale tolerance : Int} {numbers : List Int} 
  {n : Int} (h1 : 0 < tolerance) (h2 : tolerance ≤ 100) (h3 : n ∈ numbers) (h4 : n < 0) :
  ∀ i, List.get (check_sqrt_accuracy scale tolerance numbers) i = some "no" := sorry

theorem result_matches_tolerance {scale tolerance : Int} {numbers : List Int}
  {n : Int} (h1 : 0 < tolerance) (h2 : tolerance ≤ 100) (h3 : n ∈ numbers) (h4 : 0 ≤ n) :
  let sqrt_n := sqrt n
  let sqrt_squared := sqrt_n * sqrt_n
  let diff := (tolerance * n) / 100
  ∀ i, List.get (check_sqrt_accuracy scale tolerance numbers) i = 
    some (if n - sqrt_squared ≤ diff then "yes" else "no") := sorry

theorem zero_tolerance_perfect_squares {scale : Int} {numbers : List Int}
  {n : Int} (h1 : n ∈ numbers) :
  let sqrt_n := sqrt n
  ∀ i, List.get (check_sqrt_accuracy scale 0 numbers) i =
    some (if n ≥ 0 ∧ sqrt_n * sqrt_n = n then "yes" else "no") := sorry

theorem large_tolerance_all_yes {scale tolerance : Int} {numbers : List Int}
  (h1 : tolerance ≥ 100) (h2 : ∀ n ∈ numbers, n ≥ 0) :
  ∀ x ∈ check_sqrt_accuracy scale tolerance numbers, x = "yes" := sorry

-- Apps difficulty: interview
-- Assurance level: guarded