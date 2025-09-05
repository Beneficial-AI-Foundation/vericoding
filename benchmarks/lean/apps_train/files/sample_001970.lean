We have a string of letters 'a' and 'b'. We want to perform some operations on it. On each step we choose one of substrings "ab" in the string and replace it with the string "bba". If we have no "ab" as a substring, our job is done. Print the minimum number of steps we should perform to make our job done modulo 10^9 + 7.

The string "ab" appears as a substring if there is a letter 'b' right after the letter 'a' somewhere in the string.

-----Input-----

The first line contains the initial string consisting of letters 'a' and 'b' only with length from 1 to 10^6.

-----Output-----

Print the minimum number of steps modulo 10^9 + 7.

-----Examples-----
Input
ab

Output
1

Input
aab

Output
3

-----Note-----

The first example: "ab"  →  "bba".

The second example: "aab"  →  "abba"  →  "bbaba"  →  "bbbbaa".

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible