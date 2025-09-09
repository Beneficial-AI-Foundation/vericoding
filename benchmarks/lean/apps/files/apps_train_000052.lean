/-
Harry Water, Ronaldo, Her-my-oh-knee and their friends have started a new school year at their MDCS School of Speechcraft and Misery. At the time, they are very happy to have seen each other after a long time. The sun is shining, birds are singing, flowers are blooming, and their Potions class teacher, professor Snipe is sulky as usual. Due to his angst fueled by disappointment in his own life, he has given them a lot of homework in Potions class. 

Each of the n students has been assigned a single task. Some students do certain tasks faster than others. Thus, they want to redistribute the tasks so that each student still does exactly one task, and that all tasks are finished. Each student has their own laziness level, and each task has its own difficulty level. Professor Snipe is trying hard to improve their work ethics, so each student’s laziness level is equal to their task’s difficulty level. Both sets of values are given by the sequence a, where a_{i} represents both the laziness level of the i-th student and the difficulty of his task. 

The time a student needs to finish a task is equal to the product of their laziness level and the task’s difficulty. They are wondering, what is the minimum possible total time they must spend to finish all tasks if they distribute them in the optimal way. Each person should receive one task and each task should be given to one person. Print the answer modulo 10 007.

-----Input-----

The first line of input contains integer n (1 ≤ n ≤ 100 000) — the number of tasks. The next n lines contain exactly one integer number a_{i} (1 ≤ a_{i} ≤ 100 000) — both the difficulty of the initial task and the laziness of the i-th students.

-----Output-----

Print the minimum total time to finish all tasks modulo 10 007.

-----Example-----
Input
2
1
3

Output
6

-----Note-----

In the first sample, if the students switch their tasks, they will be able to finish them in 3 + 3 = 6 time units.
-/

-- <vc-helpers>
-- </vc-helpers>

def min_time_tasks (n : Nat) (difficulties : List Nat) : Nat := sorry

theorem min_time_tasks_modulo_bounds {n : Nat} {difficulties : List Nat} 
  (h : difficulties.length = n) (h1 : n > 0) : 
  min_time_tasks n difficulties < 10007 ∧ min_time_tasks n difficulties ≥ 0 := sorry

theorem min_time_tasks_permutation_invariant {n : Nat} {d1 d2 : List Nat} 
  (h : d1.length = n) (h2 : d2.length = n) (h3 : d1 = d2) :
  min_time_tasks n d1 = min_time_tasks n d2 := sorry

theorem min_time_tasks_two_elements_commutative (a b : Nat) :
  min_time_tasks 2 [a, b] = min_time_tasks 2 [b, a] := sorry

theorem min_time_tasks_two_elements_bounds (a b : Nat) 
  (h1 : a > 0) (h2 : b > 0) (h3 : a ≤ 100) (h4 : b ≤ 100) :
  min_time_tasks 2 [a, b] < 10007 ∧ min_time_tasks 2 [a, b] ≥ 0 := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval min_time_tasks 2 [1, 3]

/-
info: 10
-/
-- #guard_msgs in
-- #eval min_time_tasks 3 [1, 2, 3]

/-
info: 20
-/
-- #guard_msgs in
-- #eval min_time_tasks 4 [1, 2, 3, 4]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible