Cherry has a string S$S$ consisting of lowercase English letters. Using this string, he formed a pyramid of infinite length with certain rules:
- N$N$-th row of pyramid contains N$N$ characters.
- Each row of pyramid begins with the first character of the string.
- The subsequent characters of the row are appended to the string in cyclic fashion, until the size of string for that Row is reached (See example pyramid for better understanding).
He has another string T$T$ of smaller (or equal) size.
You are asked Q$Q$ queries. Each query is provided with a row number N$N$. The answer to the query is number of occurrences of string T$T$ in that particular row of pyramid. No of occurrences of String T$T$ in a string V$V$ would mean that you'd need to find number of substrings Vi,Vi+1...Vj$V_i, V_{i+1} ... V_j$ which are equal to String T$T$, where i≤j$i \leq j$.
For eg: If the string is code, then the pyramid will be of the form:
c
co
cod
code
codec
codeco
codecod
codecode
codecodec
codecodeco
...

-----Input:-----
- The first line contains string S$S$ — consisting of lowercase English letters.
- The second line contains string T$T$ — consisting of lowercase English letters.
- Next line contains an integer Q$Q$ — the number of queries.
- Then follow Q$Q$ lines with queries descriptions. Each of them contains a single integer N$N$ denoting the row number of pyramid.

-----Output:-----
- Print Q$Q$ lines. The i$i$-th of them should contain a integer denoting occurrences of string T$T$ in that particular row.

-----Constraints-----
- 1≤|S|≤105$1 \leq |S| \leq 10^5$
- 1≤|T|≤|S|$1 \leq |T| \leq |S|$
- 1≤Q≤105$1 \leq Q \leq 10^5$
- 1≤N≤109$1 \leq N \leq 10^9$

-----Sample Input:-----
codechef
chefcode
3
4
12
1455

-----Sample Output:-----
0
1
181

-----Explanation:-----
Pyramid will be formed as explained in the statement.
Query 1: Row number 4 of the pyramid is code. The number of occurrences of chefcode in code is 0.
Query 2: Row number 12 of the pyramid is codechefcode. The number of occurrences of chefcode in codechefcode is 1.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded