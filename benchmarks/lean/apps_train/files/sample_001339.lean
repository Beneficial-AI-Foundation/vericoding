Our Chef who was a renouned mathematician has recently got into diamonds' business. 
She has accidentally misplaced $Q$ diamonds into a jar which already had $N$ chocolates. She then started wondering about an interesting question as following. 
If we pick items one by one at random without replacement, what would be the expected number of picks required to get all diamonds out. 

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains of a single line of input, two integers $N$, $Q$. 

-----Output:-----
For each testcase, output the answer in a single line. Your answer is considered if its absolute or relative error doesn't exceed $10^{-6}$

-----Constraints-----
- $1 \leq T \leq 10^5$
- $1 \leq N \leq 10^5$
- $1 \leq Q \leq 10^5$

-----Sample Input:-----
1
2 2

-----Sample Output:-----
3.3333333333

-----EXPLANATION:-----
Here there are 2 Diamonds, 2 chocolates in the jar. 
Say C is chocolate, D is diamond.
If the random order of picking them from left to right is "CDDC", after 3 picks (CDD) all diamonds are out.
Similarly, for the remaining orders it would be the following:
"CDCD" => 4
"CCDD" => 4
"DDCC" => 2
"DCDC" => 3
"DCCD" => 4
Hence the expected number of picks would be (3+4+4+2+3+4)/6 = 3.333333

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
