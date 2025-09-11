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

/-
info: [4, 2, 0, 5, 3, 6, 1]
-/
-- #guard_msgs in
-- #eval amidakuji ["001001", "010000", "100100", "001000", "100101", "010010", "101001", "010100"]

/-
info: [1, 0, 2]
-/
-- #guard_msgs in
-- #eval amidakuji ["10"]

/-
info: [0, 1, 2, 3]
-/
-- #guard_msgs in
-- #eval amidakuji ["000"]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded