There is an automatic door at the entrance of a factory. The door works in the following way:  when one or several people come to the door and it is closed, the door immediately opens automatically and all people immediately come inside,  when one or several people come to the door and it is open, all people immediately come inside,  opened door immediately closes in d seconds after its opening,  if the door is closing and one or several people are coming to the door at the same moment, then all of them will have enough time to enter and only after that the door will close. 

For example, if d = 3 and four people are coming at four different moments of time t_1 = 4, t_2 = 7, t_3 = 9 and t_4 = 13 then the door will open three times: at moments 4, 9 and 13. It will close at moments 7 and 12.

It is known that n employees will enter at moments a, 2·a, 3·a, ..., n·a (the value a is positive integer). Also m clients will enter at moments t_1, t_2, ..., t_{m}.

Write program to find the number of times the automatic door will open. Assume that the door is initially closed.

-----Input-----

The first line contains four integers n, m, a and d (1 ≤ n, a ≤ 10^9, 1 ≤ m ≤ 10^5, 1 ≤ d ≤ 10^18) — the number of the employees, the number of the clients, the moment of time when the first employee will come and the period of time in which the door closes.

The second line contains integer sequence t_1, t_2, ..., t_{m} (1 ≤ t_{i} ≤ 10^18) — moments of time when clients will come. The values t_{i} are given in non-decreasing order.

-----Output-----

Print the number of times the door will open.

-----Examples-----
Input
1 1 3 4
7

Output
1

Input
4 3 4 2
7 9 11

Output
4

-----Note-----

In the first example the only employee will come at moment 3. At this moment the door will open and will stay open until the moment 7. At the same moment of time the client will come, so at first he will enter and only after it the door will close. Thus the door will open one time.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded