Jeff's friends know full well that the boy likes to get sequences and arrays for his birthday. Thus, Jeff got sequence p_1, p_2, ..., p_{n} for his birthday.

Jeff hates inversions in sequences. An inversion in sequence a_1, a_2, ..., a_{n} is a pair of indexes i, j (1 ≤ i < j ≤ n), such that an inequality a_{i} > a_{j} holds.

Jeff can multiply some numbers of the sequence p by -1. At that, he wants the number of inversions in the sequence to be minimum. Help Jeff and find the minimum number of inversions he manages to get.

-----Input-----

The first line contains integer n (1 ≤ n ≤ 2000). The next line contains n integers — sequence p_1, p_2, ..., p_{n} (|p_{i}| ≤ 10^5). The numbers are separated by spaces.

-----Output-----

In a single line print the answer to the problem — the minimum number of inversions Jeff can get.

-----Examples-----
Input
2
2 1

Output
0

Input
9
-2 0 -1 0 -1 2 1 0 -1

Output
6

def minInversions (n: Nat) (seq: List Int) : Nat := sorry

def countInversions (seq: List Int) : Nat := sorry

def absInt (i: Int) : Int := 
  if i < 0 then -i else i

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded
