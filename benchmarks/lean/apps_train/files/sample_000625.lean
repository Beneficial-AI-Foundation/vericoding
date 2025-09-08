/-
There are $N$ friends in a group. Each of them have $A_{i}$ candies.
Can they share all of these candies among themselves such that each one of them have equal no. of candies.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- First line of each testcase contains of a single line of input, an integer $N$ denoting no. of friends in the group. 
- Next line contains $N$ space separated integers $A_{i}$  denoting the no. candies  $i^{th}$ friend has.

-----Output:-----
For each testcase, output $"Yes"$ if it is possible to share equally else $"No"$ (without " ").

-----Constraints-----
- $1 \leq T \leq 10$
- $1 \leq N \leq 100$
- $0 \leq A_{i} \leq 1000$

-----Sample Input:-----
1

3

1 2 3

-----Sample Output:-----
Yes

-----EXPLANATION:-----
Each of them have $2$ candies after sharing.
-/

def List.sum : List Nat → Nat 
| [] => 0
| (h :: t) => h + sum t

-- <vc-helpers>
-- </vc-helpers>

def can_share_candies (n_friends : Nat) (candies : List Nat) : String := sorry

theorem can_share_candies_valid_output (n_friends : Nat) (candies : List Nat) 
  (h1 : n_friends > 0) (h2 : candies.length > 0) :
  (can_share_candies n_friends candies = "Yes" ∨ 
   can_share_candies n_friends candies = "No") := sorry

theorem can_share_candies_yes_iff_divisible (n_friends : Nat) (candies : List Nat)
  (h1 : n_friends > 0) (h2 : candies.length > 0) :
  can_share_candies n_friends candies = "Yes" ↔ 
  (List.sum candies % n_friends = 0) := sorry

theorem single_friend_always_yes (candies : List Nat) (h : candies.length > 0) :
  can_share_candies 1 candies = "Yes" := sorry

theorem zero_list_evenly_divisible (n_friends : Nat) (h : n_friends > 1) :
  can_share_candies n_friends [0] = "Yes" := sorry

/-
info: 'Yes'
-/
-- #guard_msgs in
-- #eval can_share_candies 3 [1, 2, 3]

/-
info: 'No'
-/
-- #guard_msgs in
-- #eval can_share_candies 2 [1, 2]

/-
info: 'Yes'
-/
-- #guard_msgs in
-- #eval can_share_candies 4 [2, 2, 2, 2]

-- Apps difficulty: interview
-- Assurance level: unguarded