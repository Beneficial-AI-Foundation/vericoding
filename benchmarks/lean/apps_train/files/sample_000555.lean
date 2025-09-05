Ayu loves distinct letter sequences ,a distinct letter sequence is defined by a sequence of small case english alphabets such that no character appears more then once.
But however there are two phrases that she doesn't like these phrases are "kar" and "shi" and she is given a sequence of distinct characters and she wonders how many such sequences she can form using all the characters such that these phrases don't occur.
Help her finding the number of such sequences.
New Year Gift - It is guaranteed that for sequences of length greater then 6 letters k,a,r,s,h,i will be present(we thought of being generous, thank us later :)).

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each line consists of a string $S$ (3<=s.length<=18) of distinct characters.

-----Output:-----
Print the number of sequences that can be formed by permuting all the characters such that phrases "kar" and "shi" don't occur.

-----Constraints-----
- $1 \leq T \leq 10$
- $3 \leq S.length \leq 18$

-----Sample Input:-----
2
karp
abcd

-----Sample Output:-----
22
24

def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def count_distinct_sequences (s : String) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded