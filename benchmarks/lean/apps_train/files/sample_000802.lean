/-
Doubleville, a small town in Texas, was attacked by the aliens. They have abducted some of the residents and taken them to the a spaceship orbiting around earth. After some (quite unpleasant) human experiments, the aliens cloned the victims, and released multiple copies of them back in Doubleville. So now it might happen that there are 6 identical person named Hugh F. Bumblebee: the original person and its 5 copies. The Federal Bureau of Unauthorized Cloning (FBUC) charged you with the task of determining how many copies were made from each person. To help you in your task, FBUC have collected a DNA sample from each person. All copies of the same person have the same DNA sequence, and different people have different sequences (we know that there are no identical twins in the town, this is not an issue).

-----Input-----

The input contains several blocks of test cases. Each case begins with a line containing two integers: the number 1 <= n <= 20000 people, and the length 1 <= m <= 20 of the DNA sequences. The next n lines contain the DNA sequences: each line contains a sequence of m characters, where each character is either 'A', 'C', 'G' or 'T'.

The input is terminated by a block with n = m = 0 .

-----Output-----
For each test case, you have to output n lines, each line containing a single integer. The first line contains the number of different people that were not copied. The second line contains the number of people that were copied only once (i.e., there are two identical copies for each such person.) The third line contains the number of people that are present in three identical copies, and so on: the i -th line contains the number of persons that are present in i identical copies. For example, if there are 11 samples, one of them is from John Smith, and all the others are from copies of Joe Foobar, then you have to print '1' in the first and the tenth lines, and '0' in all the other lines.

-----Example-----
Input:

9 6
AAAAAA
ACACAC
GTTTTG
ACACAC
GTTTTG
ACACAC
ACACAC
TCCCCC
TCCCCC
0 0

Output:

1
2
0
1
0
0
0
0
0
-/

def DNA := String
deriving DecidableEq

def count_dna_copies (sequences: List DNA) : List Nat :=
  sorry

abbrev List.sum (xs: List Nat) : Nat :=
  xs.foldl (· + ·) 0

-- <vc-helpers>
-- </vc-helpers>

def countOccurrences (s : DNA) (sequences : List DNA) : Nat :=
  sequences.foldl (fun acc x => if x = s then acc + 1 else acc) 0

theorem count_dna_copies_result_length 
    (sequences: List DNA) : 
    (count_dna_copies sequences).length = sequences.length :=
  sorry

theorem count_dna_copies_non_negative
    (sequences: List DNA) :
    ∀ x ∈ count_dna_copies sequences, x ≥ 0 :=
  sorry

theorem count_dna_copies_weighted_sum
    (sequences: List DNA) :
    let result := count_dna_copies sequences
    (List.range result.length).zip result
    |>.map (fun (i, v) => (i + 1) * v)
    |>.sum = sequences.length :=
  sorry

theorem count_dna_copies_matches_frequency
    (sequences: List DNA) :
    let freqs := sequences.map (fun s => countOccurrences s sequences)
    let freqCounts := (List.range sequences.length).map (fun i =>
      sequences.filter (fun s => countOccurrences s sequences = i + 1) |>.length
    )
    count_dna_copies sequences = freqCounts :=
  sorry

-- Apps difficulty: interview
-- Assurance level: guarded