The chef is having one string of English lower case alphabets only. The chef wants to remove all "abc" special pairs where a,b,c are occurring consecutively. After removing the pair, create a new string and again remove "abc" special pair from a newly formed string. Repeate the process until no such pair remains in a string.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains of a single line of input, $String$. 

-----Output:-----
For each testcase, output in a single line answer, new String with no "abc" special pair.

-----Constraints:-----
$T \leq 2 $
$1 \leq String length \leq 1000 $

-----Sample Input:-----
2
aabcc
bababccc

-----Sample Output:-----
ac
bc

-----EXPLANATION:-----
For 1) after removing "abc" at middle we get a new string as ac.
For 2) string = bababccc
newString1 = babcc  // After removing middle "abc"
newString2 = bc   //After removing "abc"

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded