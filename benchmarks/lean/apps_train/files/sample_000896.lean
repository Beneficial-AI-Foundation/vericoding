Chef has three baskets and two of them have multiple balls(Natural numbers written on them). The first basket has N balls, the second basket has M balls and the third basket is empty. Chef starts choosing all the unique balls(only occurring once in both the baskets) and puts into the third basket and throw the repetitive ones. Print numbers on the balls of the third basket in ascending order. 

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains three lines of input.
- First-line has two integers $N, M$. 
- Second-line with N space-separated numbers.
- Third-line with M space-separated numbers.

-----Output:-----
For each testcase, output in a single line answer.

-----Constraints-----
- $1 \leq T \leq 10$
- $1 \leq N \leq 10^5$
- $1 \leq M \leq 10^5$

-----Sample Input:-----
1
4 5
1 2 3 4
2 3 4 5 6

-----Sample Output:-----
1 5 6

def find_unique_balls (arr1 arr2 : List Int) : List Int := sorry

def isSorted (l : List Int) : Bool := 
  match l with
  | [] => true
  | [_] => true
  | x::y::xs => x ≤ y ∧ isSorted (y::xs)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
