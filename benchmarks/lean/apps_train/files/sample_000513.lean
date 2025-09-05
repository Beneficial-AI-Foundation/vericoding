Given an Array of length  $N$  containing elements $Ai$ ( i = 1 to n ) . You have to handle $Q$ queries on this array . Each Query is of two types k=(1 or 2). 
Type 1:- $k$ $l$ $r$ in which you have to tell whether the product of numbers in range l to r results in a perfect square or not. if product of numbers in range $l$ to$r$ is a perfect square then simply output YES else output NO.
Type 2:- $k$ $i$ $val$ Multiply the value present at index $i$ with $val$.
Note#1: 1 based indexing in each query.
Note#2: Values of prime factors of all numbers $val$ and $Ai$ is between 2 to 100 only.

-----Input:-----
- First line will contain $N$, denoting the size of the array. Then the next line follow. 
- N integers  $Ai - An$.
- Third line will contain $Q$, denoting the number of queries. Then the next $Q$ lines follow -description of each query. 
- Each query consists of either type 1 or type 2 and each query gives you three elements either
-{$k$ $l$ $r$} or {$k$ $i$ $val$}

-----Output:-----
For each  Query of Type 1 Output either "YES" or "NO" Without Quotes.

-----Constraints-----
- $1 \leq N \leq 20000$
- $1 \leq Q \leq 20000$
- $2 \leq Ai \leq 1000000$
- $1 \leq i ,l,r \leq N$
- $1 \leq val \leq 1000000$
- $1 \leq l \leq r$

-----Subtasks-----
Subtask 1 :-40 points 
- Values of prime factors of all numbers $val$ and $Ai$ is between 2 to 40 only.
Subtask 2 :- 60 points
- Original Constraints 

-----Sample Input:-----
4
2 2 3 4
4
1 1 2
1 3 4
2 3 3
1 1 4

-----Sample Output:-----
YES
NO
YES

-----EXPLANATION:-----
-Query 1 :- product of numbers in range 1 to 2=2 * 2=4 (perfect square so YES)
-Query 2:- product of numbers in range 3 to 4 = 3 * 4 = 12 (not perfect square so NO)
-Query 3:- multiply number at index3 with 3 so number at index 3= 3*3 = 9 .
-Query 4:- product of numbers in range 1 to 4 = 2 * 2 * 9 * 4 = 144 (perfect square so YES)

def perfect_square_range_query (arr : List Nat) (queries : List (Nat × Nat × Nat)) : List String :=
sorry

def is_perfect_square (n : Nat) : Bool := 
sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded