=====Function Descriptions=====
start() & end()

These expressions return the indices of the start and end of the substring matched by the group.

Code

>>> import re
>>> m = re.search(r'\d+','1234')
>>> m.end()
4
>>> m.start()
0

=====Problem Statement=====
You are given a string S.
Your task is to find the indices of the start and end of string k in S.

=====Input Format=====
The first line contains the string S.
The second line contains the string k.

=====Output Format=====
Print the tuple in this format: (start_index, end_index)

If no match is found, print (-1, -1).

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded