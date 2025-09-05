You are given a sequence of n integers a_1, a_2, ..., a_{n}. 

Determine a real number x such that the weakness of the sequence a_1 - x, a_2 - x, ..., a_{n} - x is as small as possible.

The weakness of a sequence is defined as the maximum value of the poorness over all segments (contiguous subsequences) of a sequence.

The poorness of a segment is defined as the absolute value of sum of the elements of segment.

-----Input-----

The first line contains one integer n (1 ≤ n ≤ 200 000), the length of a sequence.

The second line contains n integers a_1, a_2, ..., a_{n} (|a_{i}| ≤ 10 000).

-----Output-----

Output a real number denoting the minimum possible weakness of a_1 - x, a_2 - x, ..., a_{n} - x. Your answer will be considered correct if its relative or absolute error doesn't exceed 10^{ - 6}.

-----Examples-----
Input
3
1 2 3

Output
1.000000000000000

Input
4
1 2 3 4

Output
2.000000000000000

Input
10
1 10 2 9 3 8 4 7 5 6

Output
4.500000000000000

-----Note-----

For the first case, the optimal value of x is 2 so the sequence becomes  - 1, 0, 1 and the max poorness occurs at the segment "-1" or segment "1". The poorness value (answer) equals to 1 in this case. 

For the second sample the optimal value of x is 2.5 so the sequence becomes  - 1.5,  - 0.5, 0.5, 1.5 and the max poorness occurs on segment "-1.5 -0.5" or "0.5 1.5". The poorness value (answer) equals to 2 in this case.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded