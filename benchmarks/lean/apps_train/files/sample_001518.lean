You like tracking airplane flights a lot. Specifically, you maintain history of an airplane’s flight at several instants and record them in your notebook. Today, you have recorded N such records h1, h2, ..., hN, denoting the heights of some airplane at several instants. These records mean that airplane was first flying on height h1, then started changing its height to h2, then from h2 to h3 and so on. The airplanes are usually on cruise control while descending or ascending, so 
you can assume that plane will smoothly increase/decrease its height from hi to hi + 1 with a constant speed. You can see that during this period, the airplane will cover all possible heights in the range [min(hi, hi+1), max(hi, hi+1)] (both inclusive). It is easy to see that the plane will be at all possible heights in the range exactly a single instant of time during this ascend/descend.

You are interested in finding the maximum integer K such that the plane was at some height exactly K times during the flight.

-----Input-----
There is a single test case.
First line of the input contains an integer N denoting the number of records of heights of the plane.
Second line contains N space separated integers denoting h1, h2, ..., hN.

-----Output-----
Output a single maximum integer K in one line, such that the plane was at some height exactly K times during the flight.

-----Constraints-----
- hi ≠ hi+1

-----Subtasks-----
Subtask #1: (30 points)
- 1 ≤ N ≤ 1000
- 1 ≤ hi ≤ 1000

Subtask #2: (70 points)
- 1 ≤ N ≤ 105
- 1 ≤ hi ≤ 109

-----Example-----
Input:
5
1 2 3 2 3

Output:
3

-----Explanation-----

The flight can be draw as:

3  /\/
2 /
1

There are infinitely many heights at which the plane was 3 times during the flight, for example 2.5, 2.1. Notice that the plane was only 2 times at height 2. Moreover, there are no height at which the plane was more than 3 times, so the answer is 3.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
