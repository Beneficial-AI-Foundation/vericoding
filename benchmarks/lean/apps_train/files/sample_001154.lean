Toby has found a game to entertain himself.The game is like this:

You are in a coordinate system initially at (0,0) and you are given a sequence of steps which lead to your destination.The steps are given in the form of directions: ’U’ ,’D’ , ’L’ and ‘R’ for up, down, left and right respectively.If you are at position (x,y) then:
- U:move to (x,y+1)
- D:move to (x,y-1)
- L:move to (x-1,y)
- R:move to (x+1,y)
The sequence is provided as a string ‘s’ of characters where $s_i$ $(1 \leq i \leq N)$ is one of the direction character as mentioned above.An example of a sequence of steps is:   UULRUDR

The destination according to this string is (1,2).

You want to remove maximum number of characters from the string such that the resulting string leads to the same destination as before.
For example in the example above we can remove characters at positions 1,3,4,6 and the resulting path will be UUR which will lead to the same destination i.e (1,2).so we reduced the number of steps by 4,and this is our score.
You need to get maximum score.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- First line of each testcase contains a single integer $N$,size of string. 
- Second line of testcase contains a string $s$ of size $N$.

-----Output:-----
For each testcase, output a single line containing the maximum score possible.

-----Constraints-----
- $1 \leq T \leq 1000$
- $1 \leq N \leq 10^5$

-----Sample Input:-----
3

7

ULUDLLU

4

RUUR

4

LRLR   

-----Sample Output:-----
2

0

4    

-----EXPLANATION:-----
- 
test case 1:
The final destination after moving according to the sequence is (-3,2).

One way is to remove characters at positions 3,4 and the resulting string will be ULLLU and destination still remains (-3,2).
- 
test case 2: No character can be removed in this case.

def count_char (s : String) (c : Char) : Nat := sorry

def max_removable_steps (n : Nat) (s : String) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
