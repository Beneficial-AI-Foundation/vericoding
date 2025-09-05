The chef likes to play with numbers. He takes some integer number x, writes it down on his iPad, and then performs with it n−1 operations of the two kinds:
- divide the number x by 3 (x must be divisible by 3);
- multiply the number x by 2.
After each iteration, Chef writes down the result on his iPad and replaces x with the result. So there will be n numbers on the iPad after all.
You are given a sequence of length n — the numbers that Chef wrote down. This sequence is given in the order of the sequence can mismatch the order of the numbers written on the iPad.
Your problem is to rearrange elements of this sequence in such a way that it can match a possible Chef's game in the order of the numbers written on the board. I.e. each next number will be exactly two times the previous number or exactly one-third of the previous number.
I can give a guarantee that the answer exists.

-----Input:-----
- The first line of the input contains an integer number N i.e the number of the elements in the sequence. 
- The second line of the input contains n integer numbers a1,a2,…, an i.e rearranged (reordered) sequence that Chef can write down on the iPad.

-----Output:-----
Print N integer numbers — rearranged (reordered) input sequence that can be the sequence that Chef could write down on the iPad.
It is guaranteed that the answer exists

-----Constraints-----
- $2 \leq N \leq 100$
- $1 \leq A[i] \leq  3* 10^{18} $

-----Sample Input:-----
6
4 8 6 3 12 9

-----Sample Output:-----
9 3 6 12 4 8 

-----EXPLANATION:-----
In the first example, the given sequence can be rearranged in the following way: [9,3,6,12,4,8]. It can match possible Polycarp's game which started with x=9.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
