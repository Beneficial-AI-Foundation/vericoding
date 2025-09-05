You are given two integer sequences, each of length N: a_1, ..., a_N and b_1, ..., b_N.
There are N^2 ways to choose two integers i and j such that 1 \leq i, j \leq N. For each of these N^2 pairs, we will compute a_i + b_j and write it on a sheet of paper.
That is, we will write N^2 integers in total.
Compute the XOR of these N^2 integers.
Definition of XOR
The XOR of integers c_1, c_2, ..., c_m is defined as follows:
 - Let the XOR be X. In the binary representation of X, the digit in the 2^k's place (0 \leq k; k is an integer) is 1 if there are an odd number of integers among c_1, c_2, ...c_m whose binary representation has 1 in the 2^k's place, and 0 if that number is even.
For example, let us compute the XOR of 3 and 5. The binary representation of 3 is 011, and the binary representation of 5 is 101, thus the XOR has the binary representation 110, that is, the XOR is 6.

-----Constraints-----
 - All input values are integers.
 - 1 \leq N \leq 200,000
 - 0 \leq a_i, b_i < 2^{28}

-----Input-----
Input is given from Standard Input in the following format:
N
a_1 a_2 ... a_N
b_1 b_2 ... b_N

-----Output-----
Print the result of the computation.

-----Sample Input-----
2
1 2
3 4

-----Sample Output-----
2

On the sheet, the following four integers will be written: 4(1+3), 5(1+4), 5(2+3) and 6(2+4).

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded