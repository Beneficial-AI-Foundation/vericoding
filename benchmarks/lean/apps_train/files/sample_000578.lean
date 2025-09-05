You are given a sequence of integers $A_1,A_2,…,A_N$ and a magical non-zero integer $x$
You have to select a subsegment of sequence A (possibly empty), and replace the elements in that subsegment after dividing them by x.
Formally, replace any one subsegment $A_l, A_{l+1}, ..., A_r$ with $A_l/x, A_{l+1}/x, ..., A_r/x$ where $l \leq r$
What is the minimum possible sum you can obtain?
Note: The given operation can only be performed once

-----Input -----
- The first line of the input contains two positive integer n denoting the size of array, and x
denoting the magical integer
- Next line contains $N$ space separated integers

-----Output-----
Single line containing one real number, denoting the minimum possible sum you can obtain. Your answer will be considered correct if its absolute or relative error does not exceed $10^{-2}$

-----Constraints-----
- $1 \leq n \leq 10^3$
- $1 \leq |x| \leq 10^3$
- $ |A_i| \leq 10^3$

-----Sample Input-----
3 2
1 -2 3

-----Sample Output-----
0.5

-----Explanation-----
Array 1 -2 3, selecting subsegment {3}, you get 1 -2 1.5, which gives $sum=0.5$

def List.sum (l : List Int) : Int := 
  match l with
  | [] => 0
  | x :: xs => x + List.sum xs

def List.sumFloat (l : List Float) : Float :=
  match l with
  | [] => 0
  | x :: xs => x + List.sumFloat xs

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded