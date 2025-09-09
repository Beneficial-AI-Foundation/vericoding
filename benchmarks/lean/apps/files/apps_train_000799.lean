/-
Motu wants to learn Cricket from a coach, but firstly coach wants to test his IQ level, so he gave Motu $1$ $Red$ $ball$ and $1$ $Black$ $ball$ , and asked him to buy other $x – 1$ red balls and other $y – 1$ black balls from the market. But he put some conditions on buying balls, that if he has $R$ red and $B$ black balls then he can either buy $B$ red balls or $R$ black balls in one operation. He can perform this operation as many times as he want. But as Motu is not so good in solving problems so he needs your help. So you have to tell him whether his coach’s task possible or not.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains of a single line of input, two integers $x , y$. 

-----Output:-----
For each testcase, print $YES$, if it is possible to complete coach task, else print $NO$(without quotes) in a separate line.

-----Constraints-----
- $1 \leq T \leq 100000$
- $1 \leq x, y \leq$ 10^18

-----Sample Input:-----
2
1 2
2 3

-----Sample Output:-----
YES
YES
-/

-- <vc-helpers>
-- </vc-helpers>

def can_complete_task (x y : Nat) : String := sorry

theorem can_complete_task_output_valid (x y : Nat) 
    (hx : x > 0) (hy : y > 0) :
    can_complete_task x y = "YES" ∨ can_complete_task x y = "NO" := sorry

theorem can_complete_task_coprime (x y : Nat) 
    (hx : x > 0) (hy : y > 0) :
    can_complete_task x y = "YES" ↔ Nat.gcd x y = 1 := sorry

theorem can_complete_task_not_coprime (x y : Nat)
    (hx : x > 0) (hy : y > 0) :
    can_complete_task x y = "NO" ↔ Nat.gcd x y > 1 := sorry

theorem can_complete_task_with_one (n : Nat) (h : n > 0) :
    can_complete_task n 1 = "YES" ∧ can_complete_task 1 n = "YES" := sorry

theorem can_complete_task_same_number (n : Nat) (h : n > 0) :
    can_complete_task n n = (if n = 1 then "YES" else "NO") := sorry

/-
info: 'YES'
-/
-- #guard_msgs in
-- #eval can_complete_task 1 2

/-
info: 'YES'
-/
-- #guard_msgs in
-- #eval can_complete_task 2 3

/-
info: 'NO'
-/
-- #guard_msgs in
-- #eval can_complete_task 4 6

-- Apps difficulty: interview
-- Assurance level: unguarded