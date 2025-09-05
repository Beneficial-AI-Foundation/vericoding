You are fishing with polar bears Alice and Bob. While waiting for the fish to bite, the polar bears get bored. They come up with a game. First Alice and Bob each writes a 01-string (strings that only contain character "0" and "1") a and b. Then you try to turn a into b using two types of operations:  Write parity(a) to the end of a. For example, $1010 \rightarrow 10100$.  Remove the first character of a. For example, $1001 \rightarrow 001$. You cannot perform this operation if a is empty. 

You can use as many operations as you want. The problem is, is it possible to turn a into b?

The parity of a 01-string is 1 if there is an odd number of "1"s in the string, and 0 otherwise.

-----Input-----

The first line contains the string a and the second line contains the string b (1 ≤ |a|, |b| ≤ 1000). Both strings contain only the characters "0" and "1". Here |x| denotes the length of the string x.

-----Output-----

Print "YES" (without quotes) if it is possible to turn a into b, and "NO" (without quotes) otherwise.

-----Examples-----
Input
01011
0110

Output
YES

Input
0011
1110

Output
NO

-----Note-----

In the first sample, the steps are as follows: 01011 → 1011 → 011 → 0110

def is_possible (a b : String) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded