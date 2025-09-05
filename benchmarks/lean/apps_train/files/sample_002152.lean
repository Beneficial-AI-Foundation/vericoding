After learning a lot about space exploration, a little girl named Ana wants to change the subject.

Ana is a girl who loves palindromes (string that can be read the same backwards as forward). She has learned how to check for a given string whether it's a palindrome or not, but soon she grew tired of this problem, so she came up with a more interesting one and she needs your help to solve it:

You are given an array of strings which consist of only small letters of the alphabet. Your task is to find how many palindrome pairs are there in the array. A palindrome pair is a pair of strings such that the following condition holds: at least one permutation of the concatenation of the two strings is a palindrome. In other words, if you have two strings, let's say "aab" and "abcac", and you concatenate them into "aababcac", we have to check if there exists a permutation of this new string such that it is a palindrome (in this case there exists the permutation "aabccbaa"). 

Two pairs are considered different if the strings are located on different indices. The pair of strings with indices $(i,j)$ is considered the same as the pair $(j,i)$.

-----Input-----

The first line contains a positive integer $N$ ($1 \le N \le 100\,000$), representing the length of the input array.

Eacg of the next $N$ lines contains a string (consisting of lowercase English letters from 'a' to 'z') — an element of the input array. 

The total number of characters in the input array will be less than $1\,000\,000$.

-----Output-----

Output one number, representing how many palindrome pairs there are in the array.

-----Examples-----
Input
3
aa
bb
cd

Output
1

Input
6
aab
abcac
dffe
ed
aa
aade

Output
6

-----Note-----

The first example:  aa $+$ bb $\to$ abba. 

The second example:  aab $+$ abcac $=$ aababcac $\to$ aabccbaa aab $+$ aa $=$ aabaa abcac $+$ aa $=$ abcacaa $\to$ aacbcaa dffe $+$ ed $=$ dffeed $\to$ fdeedf dffe $+$ aade $=$ dffeaade $\to$ adfaafde ed $+$ aade $=$ edaade $\to$ aeddea

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible