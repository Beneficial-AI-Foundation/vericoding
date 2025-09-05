Indian National Olympiad in Informatics 2015
A string is any nonempty sequence of 0s and 1s. Examples of strings are 00, 101, 111000, 1, 0, 01. The length of a string is the number of symbols in it. For example, the length of 111000 is 6. If u and v are strings, then uv is the string obtained by concatenating u and v. For example if u = 110 and v = 0010 then uv = 1100010.
A string w is periodic if there exists a string v such that w = vn = vv · · · v (n times), for some n ≥ 2. Note that in this case the length of v is strictly less than that of w. For example, 110110 is periodic, because it is vv for v = 110.
Given a positive integer N , find the number of strings of length N which are not periodic. Report the answer modulo M . The non-periodic strings of length 2 are 10 and 01. The non- periodic strings of length 3 are 001, 010, 011, 100, 101, and 110.

-----Input format-----
A single line, with two space-separated integers, N and M .

-----Output format-----
A single integer, the number of non-periodic strings of length N , modulo M .

-----Test Data-----
In all subtasks, 2 ≤ M ≤ 108. The testdata is grouped into 4 subtasks.
Subtask 1 (10 marks) 1 ≤ N ≤ 4000. N is the product of two distinct prime numbers.
Subtask 2 (20 marks) 1 ≤ N ≤ 4000. N is a power of a prime number.
Subtask 3 (35 marks) 1 ≤ N ≤ 4000.
Subtask 4 (35 marks) 1 ≤ N ≤ 150000.

-----Example-----
Here is the sample input and output corresponding to the example above:

-----Sample input-----
3 176

-----Sample output-----
6

Note: Your program should not print anything other than what is specified in the output format. Please remove all diagnostic print statements before making your final submission. A program with extraneous output will be treated as incorrect!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible