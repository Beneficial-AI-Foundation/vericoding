Rani is teaching Raju maths via a game called N-Cube, which involves three sections involving N.

Rani gives Raju a number N, and Raju makes a list of Nth powers of integers in increasing order (1^N, 2^N, 3^N.. so on). This teaches him exponentiation. 
Then Raju performs the following subtraction game N times : Take all pairs of consecutive numbers in the list and take their difference. These differences then form the new list for the next iteration of the game. Eg, if N was 6, the list proceeds as [1, 64, 729, 4096 ... ] to [63, 685, 3367 ...], and so on 5 more times.
After the subtraction game, Raju has to correctly tell Rani the Nth element of the list. This number is the value of the game. 
After practice Raju became an expert in the game. To challenge him more, Rani will give two numbers M (where M is a prime) and R instead of just a single number N, and the game must start from M^(R - 1) instead of N. Since the value of the game can now become large, Raju just have to tell the largest integer K such that M^K divides this number. Since even K can be large, output K modulo 1000000007 (109+7).

-----Input-----

First line will contain T, number of testcases. Then the testcases follow
Each testcase contains of a single line of input, two integers M R

-----Output-----

For each testcase, output in a single line answer given by Raju to Rani modulo 1000000007.

-----Constraints-----

1<=T<=1000

2<=M<=109

30 points : 1<=R<=10000

70 points : 1<=R<=109

M is a prime number

-----Example-----
Input:

1

2 2

Output:

1

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
