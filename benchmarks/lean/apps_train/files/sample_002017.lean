Our beloved detective, Sherlock is currently trying to catch a serial killer who kills a person each day. Using his powers of deduction, he came to know that the killer has a strategy for selecting his next victim.

The killer starts with two potential victims on his first day, selects one of these two, kills selected victim and replaces him with a new person. He repeats this procedure each day. This way, each day he has two potential victims to choose from. Sherlock knows the initial two potential victims. Also, he knows the murder that happened on a particular day and the new person who replaced this victim.

You need to help him get all the pairs of potential victims at each day so that Sherlock can observe some pattern.

-----Input-----

First line of input contains two names (length of each of them doesn't exceed 10), the two initials potential victims. Next line contains integer n (1 ≤ n ≤ 1000), the number of days.

Next n lines contains two names (length of each of them doesn't exceed 10), first being the person murdered on this day and the second being the one who replaced that person.

The input format is consistent, that is, a person murdered is guaranteed to be from the two potential victims at that time. Also, all the names are guaranteed to be distinct and consists of lowercase English letters.

-----Output-----

Output n + 1 lines, the i-th line should contain the two persons from which the killer selects for the i-th murder. The (n + 1)-th line should contain the two persons from which the next victim is selected. In each line, the two names can be printed in any order.

-----Examples-----
Input
ross rachel
4
ross joey
rachel phoebe
phoebe monica
monica chandler

Output
ross rachel
joey rachel
joey phoebe
joey monica
joey chandler

Input
icm codeforces
1
codeforces technex

Output
icm codeforces
icm technex

-----Note-----

In first example, the killer starts with ross and rachel.   After day 1, ross is killed and joey appears.  After day 2, rachel is killed and phoebe appears.  After day 3, phoebe is killed and monica appears.  After day 4, monica is killed and chandler appears.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded
