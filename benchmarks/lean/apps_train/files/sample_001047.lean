Every day, Mike goes to his job by a bus, where he buys a ticket. On the ticket, there is a letter-code that can be represented as a string of upper-case Latin letters.
Mike believes that the day will be successful in case exactly two different letters in the code alternate.  Otherwise, he believes that the day will be unlucky. Please see note section for formal definition of alternating code.
You are given a ticket code. Please determine, whether the day will be successful for Mike or not. Print "YES" or "NO" (without quotes) corresponding to the situation.

-----Input-----
The first line of the input contains an integer T denoting the number of test cases. The description of T test cases follows.
The first and only line of each test case contains a single string S denoting the letter code on the ticket.

-----Output-----
For each test case, output a single line containing "YES" (without quotes) in case the day will be successful and "NO" otherwise.

-----Note-----
Two letters x, y where x != y are said to be alternating in a code, if code is of form "xyxyxy...".

-----Constraints-----

- 1 ≤ T ≤ 100
- S consists only of upper-case Latin letters

Subtask 1 (50 points):

- |S| = 2

Subtask 2 (50 points):

- 2 ≤ |S| ≤ 100

-----Example-----
Input:
2
ABABAB
ABC

Output:
YES
NO

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded