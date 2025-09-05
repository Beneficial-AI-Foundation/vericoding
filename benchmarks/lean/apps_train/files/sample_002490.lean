=====Problem Statement=====
You are given a string N.
Your task is to verify that N is a floating point number.

In this task, a valid float number must satisfy all of the following requirements:

> Number can start with +, - or . symbol.
For example:
✔+4.50
✔-1.0
✔.5
✔-.7
✔+.4
✖ -+4.5

> Number must contain at least 1 decimal value.
For example:
✖ 12.
✔12.0  

Number must have exactly one . symbol.
Number must not give any exceptions when converted using float(N).

=====Input Format=====
The first line contains an integer T, the number of test cases.
The next T line(s) contains a string N.

=====Constraints=====
0<T<10

=====Output Format=====
Output True or False for each test case.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible