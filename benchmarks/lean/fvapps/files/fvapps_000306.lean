-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_substrings_ones (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_substrings_ones_valid_output (s : String) : 
  count_substrings_ones s ≥ 0 ∧ count_substrings_ones s < 1000000007 :=
sorry

theorem count_substrings_ones_empty_or_zeros
  (s : String)
  (h : s = "" ∨ ∀ c, c ∈ s.data → c = '0') :
  count_substrings_ones s = 0 :=
sorry

theorem count_substrings_ones_groups 
  (ones_lengths : List Nat)
  (h : ∀ n ∈ ones_lengths, 1 ≤ n ∧ n ≤ 10) :
  let s := String.join ("0" :: (ones_lengths.map (fun n => String.mk (List.replicate n '1'))))
  let expected := ones_lengths.foldl (fun acc n => (acc + n * (n + 1) / 2) % 1000000007) 0
  count_substrings_ones s = expected :=
sorry

theorem count_substrings_ones_all_ones
  (n : Nat)
  (s : String)
  (h : s.data = List.replicate n '1') :
  count_substrings_ones s = (n * (n + 1) / 2) % 1000000007 :=
sorry
-- </vc-theorems>