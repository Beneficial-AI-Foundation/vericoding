There are N Snuke Cats numbered 1, 2, \ldots, N, where N is even.
Each Snuke Cat wears a red scarf, on which his favorite non-negative integer is written.
Recently, they learned the operation called xor (exclusive OR).What is xor?

For n non-negative integers x_1, x_2, \ldots, x_n, their xor, x_1~\textrm{xor}~x_2~\textrm{xor}~\ldots~\textrm{xor}~x_n is defined as follows:

 -  When x_1~\textrm{xor}~x_2~\textrm{xor}~\ldots~\textrm{xor}~x_n is written in base two, the digit in the 2^k's place (k \geq 0) is 1 if the number of integers among x_1, x_2, \ldots, x_n whose binary representations have 1 in the 2^k's place is odd, and 0 if that count is even. 
For example, 3~\textrm{xor}~5 = 6.

They wanted to use this operation quickly, so each of them calculated the xor of the integers written on their scarfs except his scarf.
We know that the xor calculated by Snuke Cat i, that is, the xor of the integers written on the scarfs except the scarf of Snuke Cat i is a_i.
Using this information, restore the integer written on the scarf of each Snuke Cat.

-----Constraints-----
 - All values in input are integers.
 - 2 \leq N \leq 200000
 - N is even.
 - 0 \leq a_i \leq 10^9
 - There exists a combination of integers on the scarfs that is consistent with the given information.

-----Input-----
Input is given from Standard Input in the following format:
N
a_1 a_2 \ldots a_N

-----Output-----
Print a line containing N integers separated with space.
The i-th of the integers from the left should represent the integer written on the scarf of Snuke Cat i.
If there are multiple possible solutions, you may print any of them.

-----Sample Input-----
4
20 11 9 24

-----Sample Output-----
26 5 7 22

 - 5~\textrm{xor}~7~\textrm{xor}~22 = 20
 - 26~\textrm{xor}~7~\textrm{xor}~22 = 11
 - 26~\textrm{xor}~5~\textrm{xor}~22 = 9
 - 26~\textrm{xor}~5~\textrm{xor}~7 = 24
Thus, this output is consistent with the given information.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
