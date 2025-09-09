-- <vc-helpers>
-- </vc-helpers>

def count_substrings_ones (s : String) : Nat :=
  sorry

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

/-
info: 9
-/
-- #guard_msgs in
-- #eval count_substrings_ones "0110111"

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_substrings_ones "101"

/-
info: 21
-/
-- #guard_msgs in
-- #eval count_substrings_ones "111111"

-- Apps difficulty: interview
-- Assurance level: unguarded