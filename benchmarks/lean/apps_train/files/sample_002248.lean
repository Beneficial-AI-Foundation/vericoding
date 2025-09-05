Given are integer sequence of length N, A = (A_1, A_2, \cdots, A_N), and an integer K.
For each X such that 1 \le X \le K, find the following value:
\left(\displaystyle \sum_{L=1}^{N-1} \sum_{R=L+1}^{N} (A_L+A_R)^X\right) \bmod 998244353

-----Constraints-----
 - All values in input are integers.
 -  2 \le N \le 2 \times 10^5
 -  1 \le K \le 300 
 -  1 \le A_i \le 10^8 

-----Input-----
Input is given from Standard Input in the following format:
N K
A_1 A_2 \cdots A_N

-----Output-----
Print K lines.
The X-th line should contain the value \left(\displaystyle \sum_{L=1}^{N-1} \sum_{R=L+1}^{N} (A_L+A_R)^X \right) \bmod 998244353.

-----Sample Input-----
3 3
1 2 3

-----Sample Output-----
12
50
216

In the 1-st line, we should print (1+2)^1 + (1+3)^1 + (2+3)^1 = 3 + 4 + 5 = 12.
In the 2-nd line, we should print (1+2)^2 + (1+3)^2 + (2+3)^2 = 9 + 16 + 25 = 50.
In the 3-rd line, we should print (1+2)^3 + (1+3)^3 + (2+3)^3 = 27 + 64 + 125 = 216.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded