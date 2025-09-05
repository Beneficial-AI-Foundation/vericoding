----- Statement -----

You need to find a string which has exactly K positions in it such that the character at that position comes alphabetically later than the character immediately after it. If there are many such strings, print the one which has the shortest length. If there is still a tie, print the string which comes the lexicographically earliest (would occur earlier in a dictionary).

-----Input-----
The first line contains the number of test cases T. Each test case contains an integer K (≤ 100).

-----Output-----
Output T lines, one for each test case, containing the required string.  Use only lower-case letters a-z.

-----Sample Input -----
2
1
2

-----Sample Output-----
ba
cba

def isLowercaseLetter (c : Char) : Bool := 
  let n := c.toNat
  97 ≤ n && n ≤ 122

def countDescendingPairs (s : List Char) : Nat :=
  match s with
  | [] => 0
  | [_] => 0 
  | x::y::xs => (if x > y then 1 else 0) + countDescendingPairs (y::xs)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
