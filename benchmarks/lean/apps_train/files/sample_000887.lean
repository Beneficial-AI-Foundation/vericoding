k kids seem to have visited your home for the festival. It seems like the kids
had all been fighting with each other, so you decided to keep them as far as
possible from each other. You had placed n chairs on the positive number line,
each at position x i , 1 ≤ i ≤ n. You can make the kids sit in any of the chairs.
Now you want to know the largest possible minimum distance between each kid.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains two lines. First line contains two space separated integers n and k. Second line contains n space separated values, x1, x2, x3, … ,xn.

-----Output:-----
For each test case print the largest possible minimum distance.

-----Sample Input:-----
1

2 2

1 2    

-----Sample Output:-----
1  

-----Constraints-----
- $2 \leq n \leq 100000$
- $0 \leq xi \leq 10^9$
- $k \leq n $

def find_max_min_distance (n k : Nat) (x : List Int) : Nat :=
  sorry

-- Helper functions for max/min

def listMax (xs : List Int) : Int :=
  match xs with
  | [] => 0
  | (h::t) => List.foldl max h t

def listMin (xs : List Int) : Int :=
  match xs with
  | [] => 0  
  | (h::t) => List.foldl min h t

def listToSorted (xs : List Int) : List Int :=
  match xs with
  | [] => []
  | (h::t) => h :: t -- simplified for theorem statement

-- Non-negative result

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
