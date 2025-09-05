Chuck Norris just created a universe. He has already started the space-time continuum. Now he needs to fill the universe with matter and antimatter for the avatar cycle to start.
He created $N$ distinct pairs of elementary matter and their corresponding antimatter particles. Annihilations happen only when a matter particle is placed adjacent to its corresponding antimatter particle and not when it is placed adjacent to any other matter or antimatter particle. Thus for every distinct particle of matter in the universe there exist one and only one antimatter particle that can cause its annihilation.
Chuck Norris wants to arrange all the particles in a 2-D circular pattern such that a matter particle is placed adjacent only to antimatter particles and vice versa. In how many distinct ways can he arrange them, regardless of the orientation of the arrangement, such that total annihilation of ALL particles doesn't take place i.e., $at least$ $one$ pair remain unannihilated after he arranges them in a circular pattern.
Since the total number of distinct ways can be very large, print the result modulo $1000000007$.

-----Input:-----
- First line has single integer $T$, i.e., the number of test cases
- The first and only line of each test case has a single integer $N$ i.e., number of distinct pairs of matter-antimatter particles.

-----Output:-----
- For of each test case print a single line, i.e., total number of distinct ways.

-----Constraints :-----
- $1 \leq T \leq 1000$
- $0 \leq N \leq 10^7$

-----Subtasks-----
- 
Subtask 1 : 10 pts
- $1 \leq T \leq 100$
- $0 \leq N \leq 100$ 
- 
Subtask 2 : 90 pts
- Original Constraints

-----Sample input :-----
1
3

-----Sample output :-----
8

-----Explanation:-----
For 3 pairs of elementary matter and their corresponding  antimatter particles, Chuck Norris can arrange them in 8 ways such that at least one pair of matter antimatter particles survive annihilation.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible