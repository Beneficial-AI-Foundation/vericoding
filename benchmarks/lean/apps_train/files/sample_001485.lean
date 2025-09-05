There are total N friends went to Chef's Pizza shop. There they bought a pizza. Chef divided the pizza into K equal slices. Now you have to check whether these K pizza slices can be distributed equally among the friends. Also given that every person should get at least one slice. If the above conditions are possible then print "YES" otherwise print "NO".

-----Input:-----
The first line of the input contains a single integer T denoting the number of test cases. The description of T test cases follows.
The first line of each test case contains a integers N.
The second line of each test case contains K.

-----Output:-----
For each test case, print a single line containing "YES" if the given conditions are true else "NO" if the given conditions are false.

-----Constraints-----
1<=T<=10
1<=N<=10^6
1<=K<=10^6

-----Sample Input:-----
2
10
20
12
5

-----Sample Output:-----
YES
NO

-----EXPLANATION:-----
Explanation case 1: since there are 10 friends and 20 pizza slice, so each can get 2 slices, so "YES".
Explanation case 2: Since there are 12 friends and only 5 pizza slice, so there is no way pizza slices can be distributed equally and each friend gets at least one pizza slice, so "NO".

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
