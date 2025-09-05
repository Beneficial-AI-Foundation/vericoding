One Big Software Company has n employees numbered from 1 to n. The director is assigned number 1. Every employee of the company except the director has exactly one immediate superior. The director, of course, doesn't have a superior.

We will call person a a subordinates of another person b, if either b is an immediate supervisor of a, or the immediate supervisor of a is a subordinate to person b. In particular, subordinates of the head are all other employees of the company.

To solve achieve an Important Goal we need to form a workgroup. Every person has some efficiency, expressed by a positive integer a_{i}, where i is the person's number. The efficiency of the workgroup is defined as the total efficiency of all the people included in it.

The employees of the big software company are obsessed with modern ways of work process organization. Today pair programming is at the peak of popularity, so the workgroup should be formed with the following condition. Each person entering the workgroup should be able to sort all of his subordinates who are also in the workgroup into pairs. In other words, for each of the members of the workgroup the number of his subordinates within the workgroup should be even.

Your task is to determine the maximum possible efficiency of the workgroup formed at observing the given condition. Any person including the director of company can enter the workgroup.

-----Input-----

The first line contains integer n (1 ≤ n ≤ 2·10^5) — the number of workers of the Big Software Company. 

Then n lines follow, describing the company employees. The i-th line contains two integers p_{i}, a_{i} (1 ≤ a_{i} ≤ 10^5) — the number of the person who is the i-th employee's immediate superior and i-th employee's efficiency. For the director p_1 =  - 1, for all other people the condition 1 ≤ p_{i} < i is fulfilled.

-----Output-----

Print a single integer — the maximum possible efficiency of the workgroup.

-----Examples-----
Input
7
-1 3
1 2
1 1
1 4
4 5
4 3
5 2

Output
17

-----Note-----

In the sample test the most effective way is to make a workgroup from employees number 1, 2, 4, 5, 6.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible