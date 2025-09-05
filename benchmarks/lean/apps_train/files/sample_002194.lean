You are given sequences A and B consisting of non-negative integers.
The lengths of both A and B are N, and the sums of the elements in A and B are equal.
The i-th element in A is A_i, and the i-th element in B is B_i.
Tozan and Gezan repeats the following sequence of operations:
 - If A and B are equal sequences, terminate the process.
 - Otherwise, first Tozan chooses a positive element in A and decrease it by 1.
 - Then, Gezan chooses a positive element in B and decrease it by 1.
 - Then, give one candy to Takahashi, their pet.
Tozan wants the number of candies given to Takahashi until the process is terminated to be as large as possible, while Gezan wants it to be as small as possible.
Find the number of candies given to Takahashi when both of them perform the operations optimally.

-----Constraints-----
 - 1 \leq N \leq 2 × 10^5
 - 0 \leq A_i,B_i \leq 10^9(1\leq i\leq N)
 - The sums of the elements in A and B are equal.
 - All values in input are integers.

-----Input-----
Input is given from Standard Input in the following format:
N
A_1 B_1
:
A_N B_N

-----Output-----
Print the number of candies given to Takahashi when both Tozan and Gezan perform the operations optimally.

-----Sample Input-----
2
1 2
3 2

-----Sample Output-----
2

When both Tozan and Gezan perform the operations optimally, the process will proceed as follows:
 - Tozan decreases A_1 by 1.
 - Gezan decreases B_1 by 1.
 - One candy is given to Takahashi.
 - Tozan decreases A_2 by 1.
 - Gezan decreases B_1 by 1.
 - One candy is given to Takahashi.
 - As A and B are equal, the process is terminated.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible