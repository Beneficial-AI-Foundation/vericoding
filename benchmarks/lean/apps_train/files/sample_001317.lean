There exist certain strings, known as $Unique$ $Strings$. They possess a unique property: 
- The character 'c' gets converted to "ff" and the character 'k' gets converted to "gg". Any letter besides 'c' and 'k' does not get converted to any other character.
Your job is to count the number of strings that could possibly be represented by a given unique string. Since the value could be very large, output the remainder when divided by $10^9+7$.
Note that if the given string is not a unique string, i.e. it contains either 'c' or 'k', output $0$.

-----Input:-----
- The first line of input contains a string, $s$.

-----Output:-----
- Output in a single line the possible number of strings modulo $10^9+7$.

-----Constraints-----
- $1 \leq |s| \leq 10^5$
where |s| denotes length of string.

-----Sample Input 1:-----
thing

-----Sample Input 2:-----
ggdffn

-----Sample Input 3:-----
fff

-----Sample Input 4:-----
cat

-----Sample Output 1:-----
1

-----Sample Output 2:-----
4

-----Sample Output 3:-----
3

-----Sample Output 4:-----
0

-----EXPLANATION:-----
The possible strings that can be represented by the given string in each of the examples are as follows:
$1)$ 'thing'
$2)$ 'ggdffn','kdffn','ggdcn','kdcn'
$3)$ 'fff','cf','fc'
$4)$ Since the string 'cat' contains 'c', it is certain that this string is not a unique string. Hence, the output is $0$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded