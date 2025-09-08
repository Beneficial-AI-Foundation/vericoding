/-
and Bengali as well.
There are N$N$ cats (numbered 1$1$ through N$N$) and M$M$ rats (numbered 1$1$ through M$M$) on a line. Each cat and each rat wants to move from some point to some (possibly the same) point on this line. Naturally, the cats also want to eat the rats when they get a chance. Both the cats and the rats can only move with constant speed 1$1$.
For each valid i$i$, the i$i$-th cat is initially sleeping at a point a_i$a_i$. At a time s_i$s_i$, this cat wakes up and starts moving to a final point b_i$b_i$ with constant velocity and without any detours (so it arrives at this point at the time e_i = s_i + |a_i-b_i|$e_i = s_i + |a_i-b_i|$). After it arrives at the point b_i$b_i$, it falls asleep again.
For each valid i$i$, the i$i$-th rat is initially hiding at a point c_i$c_i$. At a time r_i$r_i$, this rat stops hiding and starts moving to a final point d_i$d_i$ in the same way as the cats ― with constant velocity and without any detours, arriving at the time q_i = r_i + |c_i-d_i|$q_i = r_i + |c_i-d_i|$ (if it does not get eaten). After it arrives at the point d_i$d_i$, it hides again.
If a cat and a rat meet each other (they are located at the same point at the same time), the cat eats the rat, the rat disappears and cannot be eaten by any other cat. A sleeping cat cannot eat a rat and a hidden rat cannot be eaten ― formally, cat i$i$ can eat rat j$j$ only if they meet at a time t$t$ satisfying s_i \le t \le e_i$s_i \le t \le e_i$ and r_j \le t \le q_j$r_j \le t \le q_j$.
Your task is to find out which rats get eaten by which cats. It is guaranteed that no two cats will meet a rat at the same time.

-----Input-----
- The first line of the input contains a single integer T$T$ denoting the number of test cases. The description of T$T$ test cases follows.
- The first line of each test case contains two space-separated integers N$N$ and M$M$.
- N$N$ lines follow. For each i$i$ (1 \le i \le N$1 \le i \le N$), the i$i$-th of these lines contains three space-separated integers a_i$a_i$, b_i$b_i$ and s_i$s_i$.
- M$M$ more lines follow. For each i$i$ (1 \le i \le M$1 \le i \le M$), the i$i$-th of these lines contains three space-separated integers c_i$c_i$, d_i$d_i$ and r_i$r_i$.

-----Output-----
For each test case, print M$M$ lines. For each valid i$i$, the i$i$-th of these lines should contain a single integer ― the number of the cat that will eat the i$i$-th rat, or -1$-1$ if no cat will eat this rat.

-----Constraints-----
- 1 \le T \le 10$1 \le T \le 10$
- 0 \le N \le 1,000$0 \le N \le 1,000$
- 1 \le M \le 1,000$1 \le M \le 1,000$
- 1 \le a_i, b_i, s_i \le 10^9$1 \le a_i, b_i, s_i \le 10^9$ for each valid i$i$
- 1 \le c_i, d_i, r_i \le 10^9$1 \le c_i, d_i, r_i \le 10^9$ for each valid i$i$
- all initial and final positions of all cats and rats are pairwise distinct

-----Example Input-----
2
8 7
2 5 1
1 4 1
9 14 10
20 7 9
102 99 1
199 202 1
302 299 3
399 402 3
6 3 1
10 15 10
100 101 1
201 200 1
300 301 5
401 400 5
1000 1010 1020
8 8
2 8 2
12 18 2
22 28 4
32 38 4
48 42 2
58 52 3
68 62 1
78 72 3
3 6 3
13 19 3
21 25 3
31 39 3
46 43 4
59 53 2
65 61 4
79 71 2

-----Example Output-----
1
4
5
6
7
8
-1
1
2
3
4
5
6
7
8
-/

def absInt (n : Int) : Int :=
  if n ≥ 0 then n else -n

-- <vc-helpers>
-- </vc-helpers>

def Animal.will_collide : Animal → Animal → Option Float := sorry

def solve : Int → Int → List (Int × Int × Int) → List (Int × Int × Int) → List Int := sorry

theorem animal_init_properties (start endpoint starting_time : Int) (a : Animal) 
    (h : a = Animal.mk start endpoint starting_time sorry sorry sorry) :
  a.ending_time = starting_time + absInt (start - endpoint) ∧
  (a.velocity = 1 ∨ a.velocity = -1) ∧
  (endpoint ≥ start → a.velocity = 1) ∧
  (endpoint < start → a.velocity = -1) ∧
  a.eaten_by = (Int.neg 1, 10000000000) := sorry

theorem solve_output_properties (n m : Int) (cats rats : List (Int × Int × Int)) 
    (hn : n > 0) (hm : m > 0) :
  let result := solve n m cats rats
  List.length result = m ∧ 
  ∀ r ∈ result, -1 ≤ r ∧ r ≤ n := sorry

theorem collision_symmetry (s1 e1 t1 s2 e2 t2 : Int) :
  let a1 := Animal.mk s1 e1 t1 sorry sorry sorry
  let a2 := Animal.mk s2 e2 t2 sorry sorry sorry
  match a1.will_collide a2, a2.will_collide a1 with
  | some x, some y => Float.abs (x - y) < 0.0000000001
  | none, none => True
  | _, _ => False := sorry

theorem self_collision (start endpoint time : Int) :
  let animal := Animal.mk start endpoint time sorry sorry sorry
  match animal.will_collide animal with
  | some t => Float.toUInt64 t ≥ Float.toUInt64 (Float.ofInt time) ∧ 
              Float.toUInt64 t ≤ Float.toUInt64 (Float.ofInt animal.ending_time)  
  | none => True := sorry

-- Apps difficulty: interview
-- Assurance level: guarded