/-
Bobby has decided to hunt some Parrots. There are n horizontal branch of trees aligned parallel to each other. Branches are numbered 1 to n from top to bottom. On each branch there are some parrots sitting next to each other. Supposed there are a[i]$a[i]$ parrots sitting on the i−th$ i-th$ branch.  
Sometimes Bobby shots one of the parrot and the parrot dies (suppose that this parrots sat at the i−th$i-th$ branch). Consequently all the parrots on the i−th$i-th$ branch to the left of the dead parrot get scared and jump up on the branch number i − 1$i - 1$, if there exists no upper branch they fly away. Also all the parrots to the right of the dead parrot jump down on branch number i + 1$i + 1$, if there exists no such branch they fly away.  
Bobby has shot m parrots. You're given the initial number of parrots on each branch, tell him how many parrots are sitting on each branch after the shots.  

-----Input:-----
The first line of the input contains an integer N$N$. The next line contains a list of space-separated integers a1, a2, …, an.
The third line contains an integer M$M$. Each of the next M$M$ lines contains two integers x[i]$x[i]$ and y[i]$y[i]$. The integers mean that for the i-th time Bobby shoot the y[i]-th (from left) parrot on the x[i]-th branch. It's guaranteed there will be at least y[i] parrot on the x[i]-th branch at that moment.   

-----Output:-----
On the i−th$i-th$ line of the output print the number of parrots on the i−th$i-th$ branch.

-----Constraints-----
- 1≤N≤100$1 \leq N \leq 100$
- 0≤a[i]≤100$0 \leq a[i] \leq 100$
- 0≤M≤100$0 \leq M \leq 100$
- 1≤x[i]≤n$1 \leq x[i] \leq n$, 1≤y[i]$1 \leq y[i] $

-----Sample Input:-----
5

10 10 10 10 10

5

2 5

3 13

2 12

1 13

4 6   
3

2 4 1

1

2 2   

-----Sample Output:-----
0

12

5

0

16   
3

0

3
-/

def solve_parrot_hunt (n : Nat) (init_parrots : List Nat) (num_shots : Nat) (shots : List (Nat × Nat)) : List Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def is_valid_shot (n : Nat) (shot : Nat × Nat) : Bool :=
  1 ≤ shot.1 ∧ shot.1 ≤ n ∧ shot.2 ≥ 1

theorem solve_parrot_hunt_no_shots_preserves_input 
  (n : Nat) (init_parrots : List Nat) (h : init_parrots.length = n) :
  solve_parrot_hunt n init_parrots 0 [] = init_parrots :=
  sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible