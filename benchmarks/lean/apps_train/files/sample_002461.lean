=====Function Descriptions=====
itertools.combinations(iterable, r)
This tool returns the r length subsequences of elements from the input iterable.

Combinations are emitted in lexicographic sorted order. So, if the input iterable is sorted, the combination tuples will be produced in sorted order.

Sample Code

>>> from itertools import combinations
>>> 
>>> print list(combinations('12345',2))
[('1', '2'), ('1', '3'), ('1', '4'), ('1', '5'), ('2', '3'), ('2', '4'), ('2', '5'), ('3', '4'), ('3', '5'), ('4', '5')]
>>> 
>>> A = [1,1,3,3,3]
>>> print list(combinations(A,4))
[(1, 1, 3, 3), (1, 1, 3, 3), (1, 1, 3, 3), (1, 3, 3, 3), (1, 3, 3, 3)]

=====Problem Statement=====
You are given a string S.
Your task is to print all possible combinations, up to size k, of the string in lexicographic sorted order.

=====Constraints=====
0<k≤len(S)

=====Input Format=====
A single line containing the string S and integer value k separated by a space.

=====Output Format=====
Print the different combinations of string S on separate lines.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
