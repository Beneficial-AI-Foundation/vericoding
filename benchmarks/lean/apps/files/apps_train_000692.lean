/-
The notorious hacker group "Sed" managed to obtain a string $S$ from their secret sources. The string contains only lowercase English letters along with the character '?'.
A substring of $S$ is a contiguous subsequence of that string. For example, the string "chef" is a substring of the string "codechef", but the string "codeh" is not a substring of "codechef".
A substring of $S$ is good if it is possible to choose a lowercase English letter $C$ such that the following process succeeds:
- Create a string $R$, which is a copy of the substring, but with each '?' replaced by the letter $c$. Note that all occurrences of '?' must be replaced by the same letter.
- For each lowercase English letter:
- Compute the number of times it occurs in $S$ and the number of times it occurs in $R$; let's denote them by $A$ and $B$ respectively. The '?' characters in the original string $S$ are ignored when computing $A$.
- Check the parity of $A$ and $B$. If they do not have the same parity, i.e. one of them is even while the other is odd, then this process fails.
- If the parities of the number of occurrences in $S$ and $R$ are the same for each letter, the process succeeds.
For different substrings, we may choose different values of $C$.
Help Sed find the number of good substrings in the string $S$.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains a single string $S$.

-----Output-----
For each test case, print a single line containing one integer ― the number of good substrings.

-----Constraints-----
- $1 \le T \le 10^5$
- $1 \le S \le 10^5$
- $S$ contains only lowercase English letters ('a' through 'z') and '?'
- the sum of $|S|$ over all test cases does not exceed $10^5$

-----Example Input-----
5
aa?
a???
????
asfhaslskfak
af??avvnfed?fav?faf????

-----Example Output-----
2
6
4
2
27

-----Explanation-----
Example case 1: All letters occur an even number of times in $S$. The six substrings of $S$ are "a", "a", "?", "aa", "a?" and "aa?" (note that "a" is counted twice). Which of them are good?
- "a" is not good as 'a' occurs an odd number of times in this substring and there are no '?' to replace.
- "?" is also not good as replacing '?' by any letter causes this letter to occur in $R$ an odd number of times.
- "aa" is a good substring because each letter occurs in it an even number of times and there are no '?' to replace.
- "a?" is also a good substring. We can replace '?' with 'a'. Then, $R$ is "aa" and each letter occurs in this string an even number of times. Note that replacing '?' e.g. with 'b' would not work ($R$ would be "ab", where both 'a' and 'b' occur an odd number of times), but we may choose the replacement letter $C$ appropriately.
- "aa?" is not a good substring. For any replacement letter $C$, we find that $C$ occurs an odd number of times in $R$.
Example case 2: We especially note that "a???" is not a good substring. Since all '?' have to be replaced by the same character, we can only get strings of the form "aaaa", "abbb", "accc", etc., but none of them match the criteria for a good substring.
Example case 3: Any substring with even length is good.
-/

-- <vc-helpers>
-- </vc-helpers>

def solve (s : String) : Nat := sorry

theorem solve_single_wildcard : solve "aa?" = 2 := sorry

theorem solve_multi_wildcard : solve "a???" = 6 := sorry

theorem solve_all_wildcards : solve "????" = 4 := sorry

-- Apps difficulty: interview
-- Assurance level: guarded