/-
Chef wants to teach a lesson of sharing to the students.
There are $N$ students (numbered from $1$ to $N$ from left to right) who are asked to stand in a row. Initially Chef gave $A$$i$ candies to the $i$$th$ child. In one operation any child can give any number of candies to the child standing to his immediate left (i.e. $i$$th$ child can give any amount of candies to the $(i-1)$$th$ child. In particular 1st child cannot give his candies to anyone).  
He asked them to minimize the maximum value of candies a student can possess after performing any number of operations (possibly zero). 
Help the students finding such maximum value.

-----Input:-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- First line of each test case contains a single integer $N$ denoting the number of students.
- Second line contains $N$ space-separated integers $A$$1$,$A$$2$,$.....$ $A$$N$ denoting the initial amount of candies chef gave to them.

-----Output:-----
- For each test case, print a single line containing one integer ― maximum value after sharing.

-----Constraints-----
- $1 \leq T \leq 100$
- $1 \leq N \leq 10^5$
- $0$ $\leq$ $A$$i$ $\leq$ $10^9$
- Sum of $N$ over all Test Cases does not exceed $10^5$

-----Sample Input-----
2 
5 
1 2 3 4 5 
5
5 4 3 2 1

-----Sample Output-----
3 
5  

-----Explanation-----
- 
For First Test Case:
The $5$$th$ student will give $2$ candies to $4$$th$ student and $4$$th$ will give $3$ candies to $3$$rd$ and $3$$rd$ will give $3$ candies to $2$$nd$ and $2$$nd$ will give $2$ candies to $1$$st$. So finally the number of candies that they will have are 
$[3,3,3,3,3]$ and the value of maximum candies is $3$.
- 
For Second Test Case:
Sharing to the left student will not change the maximum value as $1$$st$ cannot share to anyone. So the maximum value will remain $5$.
-/

def List.sum : List Nat → Nat 
  | [] => 0
  | (x::xs) => x + xs.sum

def List.maximum : List Nat → Nat
  | [] => 0
  | [x] => x 
  | (x::xs) => max x (xs.maximum)

-- <vc-helpers>
-- </vc-helpers>

def solve_candy_sharing (n : Nat) (arr : List Nat) : Nat :=
  sorry

theorem solve_candy_sharing_bounds 
  {n : Nat} {arr : List Nat}
  (h1 : n > 0)
  (h2 : arr.length = n)
  (h3 : ∀ x ∈ arr, x > 0 ∧ x ≤ 1000)
  : solve_candy_sharing n arr ≥ (arr.sum + n - 1) / n ∧ 
    solve_candy_sharing n arr ≤ arr.maximum :=
  sorry

theorem solve_candy_sharing_single
  (n : Nat)
  (h1 : n > 0)
  (h2 : n ≤ 100)
  : solve_candy_sharing 1 [n] = n :=
  sorry

theorem solve_candy_sharing_multiple_elements
  {n : Nat} {arr : List Nat}
  (h1 : arr.length = n)
  (h2 : n ≥ 2)
  (h3 : ∀ x ∈ arr, x > 0 ∧ x ≤ 1000)
  : solve_candy_sharing n arr > 0 :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_candy_sharing 5 arr1.copy()

/-
info: 5
-/
-- #guard_msgs in
-- #eval solve_candy_sharing 5 arr2.copy()

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_candy_sharing 3 arr3.copy()

-- Apps difficulty: interview
-- Assurance level: unguarded