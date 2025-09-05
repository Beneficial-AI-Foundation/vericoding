You are given a sequence a consisting of n integers. Find the maximum possible value of $a_{i} \operatorname{mod} a_{j}$ (integer remainder of a_{i} divided by a_{j}), where 1 ≤ i, j ≤ n and a_{i} ≥ a_{j}.

-----Input-----

The first line contains integer n — the length of the sequence (1 ≤ n ≤ 2·10^5). 

The second line contains n space-separated integers a_{i} (1 ≤ a_{i} ≤ 10^6).

-----Output-----

Print the answer to the problem.

-----Examples-----
Input
3
3 4 5

Output
2

def find_max_remainder (nums : List Nat) : Nat := sorry

def list_maximum (nums : List Nat) : Nat := 
  match nums with
  | [] => 0
  | (x::xs) => List.foldl Nat.max x xs

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded
