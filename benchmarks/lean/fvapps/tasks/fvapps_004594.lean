-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def amidakuji (ladder : List (List Char)) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem amidakuji_length
  {ladder : List (List Char)}
  (h1 : ∀ row ∈ ladder, row.length = (ladder.head!).length)
  (h2 : ∀ row ∈ ladder, ∀ c ∈ row, c = '0' ∨ c = '1') :
  (amidakuji ladder).length = (ladder.head!).length + 1 :=
  sorry

theorem amidakuji_permutation
  {ladder : List (List Char)}
  (h1 : ∀ row ∈ ladder, row.length = (ladder.head!).length)
  (h2 : ∀ row ∈ ladder, ∀ c ∈ row, c = '0' ∨ c = '1') :
  ∃ perm : List Nat,
    List.Perm perm (List.range ((ladder.head!).length + 1)) ∧
    amidakuji ladder = perm :=
  sorry

theorem amidakuji_empty_rows
  {ladder : List (List Char)}
  (h : ∀ row ∈ ladder, row.isEmpty) :
  amidakuji ladder = List.range 1 :=
  sorry

theorem amidakuji_no_swaps
  {ladder : List (List Char)}
  (h1 : ∀ row ∈ ladder, row.length = (ladder.head!).length)
  (h2 : ∀ row ∈ ladder, ∀ c ∈ row, c = '0') :
  amidakuji ladder = List.range ((ladder.head!).length + 1) :=
  sorry
-- </vc-theorems>