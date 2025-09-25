-- <vc-preamble>
def DNA := String
deriving DecidableEq

def count_dna_copies (sequences: List DNA) : List Nat :=
  sorry

abbrev List.sum (xs: List Nat) : Nat :=
  xs.foldl (· + ·) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countOccurrences (s : DNA) (sequences : List DNA) : Nat :=
  sequences.foldl (fun acc x => if x = s then acc + 1 else acc) 0
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>