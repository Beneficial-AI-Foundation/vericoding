After acquiring an extraordinary amount of knowledge through programming contests, Malvika decided to harness her expertise to train the next generation of Indian programmers. So, she decided to hold a programming camp. In the camp, she held a discussion session for n members (n-1 students, and herself). They are sitting in a line from left to right numbered through 1 to n.

Malvika is sitting in the nth spot. She wants to teach m topics of competitive programming to the students. As the people taking part in the camp are all newbies, they know none of the topics being taught, i.e., initially, the first n - 1 people in the line know none of the topics, while the nth knows all of them.

It takes one hour for a person to learn a topic from his neighbour. Obviously, one person cannot both teach a topic as well as learn one during the same hour. That is, in any particular hour, a person can either teach a topic that he knows to one of his neighbors, or he can learn a topic from one of his neighbors, or he can sit idly. It is also obvious that if person x is learning from person y at a particular hour, then person y must be teaching person x at that hour.

Also, note that people can work parallely too, i.e., in the same hour when the 4th person is teaching the 3rd person, the 1st person can also teach the 2nd or learn from 2nd.

Find out the minimum number of hours needed so that each person learns all the m topics.

-----Input-----
- The first line of input contains a single integer T denoting number of test cases.
- The only line of each test case contains two space separated integers n, m as defined in the statement.

-----Output-----
- For each test case, output a single integer in a line corresponding to the answer of the problem.

-----Constraints-----
- 1 ≤ T, n, m ≤ 100

-----Example-----
Input:
2
2 1
3 2

Output:
1
4

-----Explanation-----
In the first example, there are two people. Second person is Malvika and she has to teach only one topic to the first person. It will take only one hour to do so.

In the second example, there are three people. The 3rd person is Malvika and she has to teach only two topics to 1st and 2nd person. In the 1st hour, she teaches the 1st topic to the 2nd person. Now, in the 2nd hour, the 2nd person will teach the 1st topic to the 1st person. In the 3rd hour, Malvika will teach the 2nd topic to the 2nd person. Now the 2nd person will teach that topic to the 1st in the 4th hour. So, it takes a total of 4 hours for all the people to know all the topics.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
